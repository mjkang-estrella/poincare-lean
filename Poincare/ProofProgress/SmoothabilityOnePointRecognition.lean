import Poincare.Smoothability
import Poincare.TopologyExtraction

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
A recognition homeomorphism to the one-point compactification model transports
the concrete smooth compactification atlas back to the source.
-/
@[reducible] noncomputable def homeomorphToOnePoint_threeSpace_smoothChartedSpace
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ChartedSpace ThreeManifoldModel M := by
  letI : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_smoothChartedSpace
  exact e.symm.isLocalHomeomorph.chartedSpace e.symm.surjective

/--
Any source recognized as the one-point compactification inherits a genuine
smooth 3-manifold structure by transporting the concrete compactification
smooth atlas.
-/
theorem homeomorphToOnePoint_threeSpace_smoothManifold
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    letI : ChartedSpace ThreeManifoldModel M :=
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e
    IsManifold (𝓡 3) ∞ M := by
  letI : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_smoothChartedSpace
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  haveI : IsManifold (𝓡 3) ∞
      (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_smoothManifold
  exact smoothManifold_of_homeomorph_transportedChartedSpace e

/--
The transported smooth compactification atlas supplies the exact `C¹`
surgery-model manifold evidence consumed by the Ricci-flow-with-surgery layer.
-/
theorem homeomorphToOnePoint_threeSpace_surgeryModel_isManifold
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    letI : ChartedSpace ThreeManifoldModel M :=
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e
    IsManifold ThreeManifoldModelWithCorners 1 M := by
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  exact surgeryModel_isManifold_of_smoothManifold M
    (homeomorphToOnePoint_threeSpace_smoothManifold e)

/--
Recognition as the one-point compactification gives the full topological and
smooth manifold instance payload required to run the surgery layer on the
recognized source, using the transported smooth compactification atlas.
-/
theorem smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      Nonempty M := by
  rcases h with ⟨e⟩
  letI : T2Space (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_t2Space
  letI : CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_compactSpace
  letI : SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    onePoint_threeSpace_simplyConnectedSpace_of_sourceChoiceCollapse
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  let simple : SimplyConnectedSpace M :=
    e.toHomotopyEquiv.simplyConnectedSpace
  let smooth : IsManifold ThreeManifoldModelWithCorners 1 M := by
    letI : ChartedSpace ThreeManifoldModel M := charted
    exact homeomorphToOnePoint_threeSpace_surgeryModel_isManifold e
  let nonempty : Nonempty M := by
    letI : SimplyConnectedSpace M := simple
    infer_instance
  exact ⟨e.symm.t2Space, charted, simple, e.symm.compactSpace, smooth, nonempty⟩

/--
Recognition as the one-point compactification supplies the transported surgery
prerequisites together with coherent first Moise witnesses from the same
recognition proof.
-/
theorem smoothability_surgery_and_moise_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ triangulation : HasMoiseTriangulation M,
      localCharts.onePointRecognition = h ∧
        triangulation.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty,
      HasMoiseLocalTriangulationCharts.ofOnePointRecognition h,
      HasMoiseTriangulation.ofOnePointRecognition h, rfl, rfl⟩

/--
Recognition as the one-point compactification supplies the transported surgery
prerequisites together with coherent local Moise charts, locally finite
refinement, and global Moise triangulation witnesses from the same recognition
proof.
-/
theorem smoothability_surgery_and_moise_refinement_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ refinement : HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ triangulation : HasMoiseTriangulation M,
      localCharts.onePointRecognition = h ∧
        refinement.onePointRecognition = h ∧
        triangulation.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let localCharts := HasMoiseLocalTriangulationCharts.ofOnePointRecognition h
  let refinement :=
    HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty,
      localCharts, refinement,
      HasMoiseTriangulation.ofOnePointRecognition h, rfl, rfl, rfl⟩

/--
Recognition as the one-point compactification carries the local Moise data all
the way to a compatible PL atlas, with the simplicial-complex and chart
compatibility witnesses tied to the same recognition proof.
-/
theorem smoothability_moise_to_pl_atlas_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ refinement : HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ chartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plTransition : HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
      localCharts.onePointRecognition = h ∧
        refinement.onePointRecognition = h ∧
        simplicialComplex.onePointRecognition = h ∧
        chartTriangulations.onePointRecognition = h ∧
        triangulation.onePointRecognition = h ∧
        plStructure.onePointRecognition = h ∧
        plTransition.onePointRecognition = h ∧
        plAtlas.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let localCharts := HasMoiseLocalTriangulationCharts.ofOnePointRecognition h
  let refinement :=
    HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl
  let simplicialComplex :=
    HasMoiseSimplicialComplex.ofOnePointRecognition h rfl
  let chartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts simplicialComplex :=
    HasMoiseCompatibleChartTriangulations.ofOnePointRecognition
      (localCharts := localCharts) (simplicialComplex := simplicialComplex)
      h rfl
  let triangulation := HasMoiseTriangulation.ofOnePointRecognition h
  let plStructure : HasCompatiblePLStructure M triangulation :=
    HasCompatiblePLStructure.ofOnePointRecognition
      (triangulation := triangulation) h
  let plTransition :
      HasPLTransitionCompatibility M triangulation plStructure :=
    HasPLTransitionCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  let plAtlas : HasCompatiblePLAtlas M triangulation plStructure :=
    HasCompatiblePLAtlas.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, localCharts, refinement,
      simplicialComplex, chartTriangulations, triangulation, plStructure,
      plTransition, plAtlas, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Recognition as the one-point compactification carries the compatible PL atlas
through the PL-manifold atlas tail, with collar, homeomorphism, and maximality
witnesses tied to the same recognition proof.
-/
theorem smoothability_pl_manifold_atlas_tail_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ refinement : HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ chartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plTransition : HasPLTransitionCompatibility M triangulation plStructure,
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
      localCharts.onePointRecognition = h ∧
        refinement.onePointRecognition = h ∧
        simplicialComplex.onePointRecognition = h ∧
        chartTriangulations.onePointRecognition = h ∧
        triangulation.onePointRecognition = h ∧
        plStructure.onePointRecognition = h ∧
        plTransition.onePointRecognition = h ∧
        plAtlas.onePointRecognition = h ∧
        plManifoldAtlas.onePointRecognition = h ∧
        plCollarNeighborhoodCompatibility.onePointRecognition = h ∧
        plHomeomorphismCompatibility.onePointRecognition = h ∧
        plAtlasMaximality.onePointRecognition = h := by
  rcases smoothability_moise_to_pl_atlas_core_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty, localCharts, refinement,
      simplicialComplex, chartTriangulations, triangulation, plStructure,
      plTransition, plAtlas, hlocal, hrefinement, hsimplicial,
      hchartTriangulations, htriangulation, hplStructure, hplTransition,
      hplAtlas⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas :=
    HasPLManifoldAtlas.ofOnePointRecognition h
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas :=
    HasPLCollarNeighborhoodCompatibility.ofOnePointRecognition h
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas :=
    HasPLHomeomorphismCompatibility.ofOnePointRecognition h
      (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas :=
    HasPLAtlasMaximality.ofOnePointRecognition h
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, localCharts, refinement,
      simplicialComplex, chartTriangulations, triangulation, plStructure,
      plTransition, plAtlas, plManifoldAtlas,
      plCollarNeighborhoodCompatibility, plHomeomorphismCompatibility,
      plAtlasMaximality, hlocal, hrefinement, hsimplicial,
      hchartTriangulations, htriangulation, hplStructure, hplTransition,
      hplAtlas, rfl, rfl, rfl, rfl⟩

/--
Recognition as the one-point compactification carries the compatible PL atlas
through the dimension-three PL smoothing theorem and its compatibility,
uniqueness, and local-model witnesses.
-/
theorem smoothability_moise_to_pl_smoothing_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ refinement : HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ chartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing,
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
      localCharts.onePointRecognition = h ∧
        refinement.onePointRecognition = h ∧
        simplicialComplex.onePointRecognition = h ∧
        chartTriangulations.onePointRecognition = h ∧
        triangulation.onePointRecognition = h ∧
        plStructure.onePointRecognition = h ∧
        plAtlas.onePointRecognition = h ∧
        plSmoothingExistence.onePointRecognition = h ∧
        plSmoothingObstructionVanishing.onePointRecognition = h ∧
        plMicrobundleSmoothing.onePointRecognition = h ∧
        plSmoothing.onePointRecognition = h ∧
        plSmoothingCompatibility.onePointRecognition = h ∧
        plSmoothingUniqueness.onePointRecognition = h ∧
        plSmoothingLocalModelCompatibility.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let localCharts := HasMoiseLocalTriangulationCharts.ofOnePointRecognition h
  let refinement :=
    HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl
  let simplicialComplex :=
    HasMoiseSimplicialComplex.ofOnePointRecognition h rfl
  let chartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts simplicialComplex :=
    HasMoiseCompatibleChartTriangulations.ofOnePointRecognition
      (localCharts := localCharts) (simplicialComplex := simplicialComplex)
      h rfl
  let triangulation := HasMoiseTriangulation.ofOnePointRecognition h
  let plStructure : HasCompatiblePLStructure M triangulation :=
    HasCompatiblePLStructure.ofOnePointRecognition
      (triangulation := triangulation) h
  let plAtlas : HasCompatiblePLAtlas M triangulation plStructure :=
    HasCompatiblePLAtlas.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  let plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas :=
    HasPLSmoothingExistence.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas :=
    HasPLSmoothingObstructionVanishing.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing :=
    HasPLMicrobundleSmoothing.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas)
      (plSmoothingExistence := plSmoothingExistence)
      (plSmoothingObstructionVanishing := plSmoothingObstructionVanishing)
      h rfl rfl rfl rfl
  let plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas :=
    HasPLSmoothingTheorem.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  let plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingUniqueness.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  let plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingLocalModelCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, localCharts, refinement,
      simplicialComplex, chartTriangulations, triangulation, plStructure,
      plAtlas, plSmoothingExistence, plSmoothingObstructionVanishing,
      plMicrobundleSmoothing, plSmoothing, plSmoothingCompatibility,
      plSmoothingUniqueness, plSmoothingLocalModelCompatibility,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Recognition as the one-point compactification carries the PL smoothing theorem
through construction of the smooth structure, smooth atlas, PL compatibility,
maximality, uniqueness, and transition-smoothness witnesses.
-/
theorem smoothability_moise_to_smooth_atlas_core_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ refinement : HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ chartTriangulations :
      HasMoiseCompatibleChartTriangulations M localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
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
      localCharts.onePointRecognition = h ∧
        refinement.onePointRecognition = h ∧
        simplicialComplex.onePointRecognition = h ∧
        chartTriangulations.onePointRecognition = h ∧
        triangulation.onePointRecognition = h ∧
        plStructure.onePointRecognition = h ∧
        plAtlas.onePointRecognition = h ∧
        plSmoothing.onePointRecognition = h ∧
        smoothStructure.onePointRecognition = h ∧
        smoothAtlasConstruction.onePointRecognition = h ∧
        smoothAtlasPLCompatibility.onePointRecognition = h ∧
        smoothAtlasMaximality.onePointRecognition = h ∧
        smoothAtlasUniqueness.onePointRecognition = h ∧
        smoothStructureUniqueness.onePointRecognition = h ∧
        smoothTransitionCompatibility.onePointRecognition = h ∧
        smoothAtlasTransitionSmoothness.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let localCharts := HasMoiseLocalTriangulationCharts.ofOnePointRecognition h
  let refinement :=
    HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl
  let simplicialComplex :=
    HasMoiseSimplicialComplex.ofOnePointRecognition h rfl
  let chartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts simplicialComplex :=
    HasMoiseCompatibleChartTriangulations.ofOnePointRecognition
      (localCharts := localCharts) (simplicialComplex := simplicialComplex)
      h rfl
  let triangulation := HasMoiseTriangulation.ofOnePointRecognition h
  let plStructure : HasCompatiblePLStructure M triangulation :=
    HasCompatiblePLStructure.ofOnePointRecognition
      (triangulation := triangulation) h
  let plAtlas : HasCompatiblePLAtlas M triangulation plStructure :=
    HasCompatiblePLAtlas.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  let plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas :=
    HasPLSmoothingTheorem.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let smoothStructure : HasThreeManifoldSmoothStructure M :=
    HasThreeManifoldSmoothStructure.ofOnePointRecognition h
  let smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure :=
    HasSmoothAtlasConstruction.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure) h rfl rfl rfl rfl
  let smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction :=
    HasSmoothAtlasPLCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure)
      (smoothAtlasConstruction := smoothAtlasConstruction)
      h rfl rfl rfl rfl rfl
  let smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure :=
    HasSmoothAtlasMaximality.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure) h rfl rfl rfl rfl
  let smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure :=
    HasSmoothAtlasUniqueness.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure :=
    HasSmoothStructureUniquenessUpToDiffeomorphism.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure :=
    HasSmoothTransitionCompatibility.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility :=
    HasSmoothAtlasTransitionSmoothness.ofOnePointRecognition
      (smoothStructure := smoothStructure)
      (smoothTransitionCompatibility := smoothTransitionCompatibility)
      h rfl rfl
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, localCharts, refinement,
      simplicialComplex, chartTriangulations, triangulation, plStructure,
      plAtlas, plSmoothing, smoothStructure, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Recognition as the one-point compactification supplies the full
`SmoothStructureDerivationStatement`: the Moise, PL, smoothing, smooth-atlas,
transition, and derivation witnesses are all constructed from the same
recognition proof.
-/
theorem smoothability_smooth_structure_derivation_statement_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
      SmoothStructureDerivationStatement M smoothStructure ∧
        smoothStructure.onePointRecognition = h := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, smooth, nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  let localCharts := HasMoiseLocalTriangulationCharts.ofOnePointRecognition h
  let refinement :=
    HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl
  let simplicialComplex :=
    HasMoiseSimplicialComplex.ofOnePointRecognition h rfl
  let chartTriangulations :
      HasMoiseCompatibleChartTriangulations
        M localCharts simplicialComplex :=
    HasMoiseCompatibleChartTriangulations.ofOnePointRecognition
      (localCharts := localCharts) (simplicialComplex := simplicialComplex)
      h rfl
  let triangulation := HasMoiseTriangulation.ofOnePointRecognition h
  let simplicialApproximation :
      HasMoiseSimplicialApproximation
        M localCharts simplicialComplex triangulation :=
    HasMoiseSimplicialApproximation.ofOnePointRecognition
      (localCharts := localCharts) (simplicialComplex := simplicialComplex)
      (triangulation := triangulation) h rfl
  let starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation :=
    HasMoiseStarNeighborhoodBasis.ofOnePointRecognition
      (localCharts := localCharts) (triangulation := triangulation) h rfl
  let barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation :=
    HasMoiseBarycentricSubdivisionControl.ofOnePointRecognition
      (triangulation := triangulation) h
  let regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation :=
    HasMoiseRegularNeighborhoodCompatibility.ofOnePointRecognition
      (triangulation := triangulation) h
  let triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation :=
    HasMoiseTriangulationLocalFiniteness.ofOnePointRecognition
      (triangulation := triangulation) h
  let linkCompatibility : HasMoiseLinkCompatibility M triangulation :=
    HasMoiseLinkCompatibility.ofOnePointRecognition
      (triangulation := triangulation) h
  let plManifoldRecognition :
      HasMoisePLManifoldRecognition M triangulation linkCompatibility :=
    HasMoisePLManifoldRecognition.ofOnePointRecognition
      (triangulation := triangulation)
      (linkCompatibility := linkCompatibility) h
  let triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M localCharts triangulation :=
    HasMoiseTriangulationHomeomorphism.ofOnePointRecognition
      (localCharts := localCharts) (triangulation := triangulation) h rfl
  let moiseCompatibility :
      HasMoiseTriangulationCompatibility M localCharts triangulation :=
    HasMoiseTriangulationCompatibility.ofOnePointRecognition
      (localCharts := localCharts) (triangulation := triangulation) h rfl
  let triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation :=
    HasMoiseTriangulationUniqueness.ofOnePointRecognition
      (triangulation := triangulation) h
  let hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree
        M triangulation triangulationUniqueness :=
    HasMoiseHauptvermutungDimensionThree.ofOnePointRecognition
      (triangulation := triangulation)
      (triangulationUniqueness := triangulationUniqueness) h
  let plStructure : HasCompatiblePLStructure M triangulation :=
    HasCompatiblePLStructure.ofOnePointRecognition
      (triangulation := triangulation) h
  let plTransition :
      HasPLTransitionCompatibility M triangulation plStructure :=
    HasPLTransitionCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  let plAtlas : HasCompatiblePLAtlas M triangulation plStructure :=
    HasCompatiblePLAtlas.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure) h rfl
  let plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas :=
    HasPLManifoldAtlas.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas :=
    HasPLCollarNeighborhoodCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas :=
    HasPLHomeomorphismCompatibility.ofOnePointRecognition
      (localCharts := localCharts) (triangulation := triangulation)
      (plStructure := plStructure) (plAtlas := plAtlas) h rfl rfl rfl
  let plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas :=
    HasPLAtlasMaximality.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas :=
    HasPLSmoothingExistence.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas :=
    HasPLSmoothingObstructionVanishing.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M triangulation plStructure plAtlas
        plSmoothingExistence plSmoothingObstructionVanishing :=
    HasPLMicrobundleSmoothing.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas)
      (plSmoothingExistence := plSmoothingExistence)
      (plSmoothingObstructionVanishing := plSmoothingObstructionVanishing)
      h rfl rfl rfl rfl
  let plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas :=
    HasPLSmoothingTheorem.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) h rfl rfl
  let plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  let plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingUniqueness.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  let plSmoothingLocalModelCompatibility :
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing :=
    HasPLSmoothingLocalModelCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      h rfl rfl rfl
  let smoothStructure : HasThreeManifoldSmoothStructure M :=
    HasThreeManifoldSmoothStructure.ofOnePointRecognition h
  let smoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure :=
    HasSmoothAtlasConstruction.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure) h rfl rfl rfl rfl
  let smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction :=
    HasSmoothAtlasPLCompatibility.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure)
      (smoothAtlasConstruction := smoothAtlasConstruction)
      h rfl rfl rfl rfl rfl
  let smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure :=
    HasSmoothAtlasMaximality.ofOnePointRecognition
      (triangulation := triangulation) (plStructure := plStructure)
      (plAtlas := plAtlas) (smoothingTheorem := plSmoothing)
      (smoothStructure := smoothStructure) h rfl rfl rfl rfl
  let smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure :=
    HasSmoothAtlasUniqueness.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism M smoothStructure :=
    HasSmoothStructureUniquenessUpToDiffeomorphism.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure :=
    HasSmoothTransitionCompatibility.ofOnePointRecognition
      (smoothStructure := smoothStructure) h rfl
  let smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility :=
    HasSmoothAtlasTransitionSmoothness.ofOnePointRecognition
      (smoothStructure := smoothStructure)
      (smoothTransitionCompatibility := smoothTransitionCompatibility)
      h rfl rfl
  let smoothStructureDerivation :
      HasSmoothStructureDerivation
        M localCharts refinement simplicialComplex chartTriangulations
        triangulation simplicialApproximation starNeighborhoodBasis
        barycentricSubdivision regularNeighborhoodCompatibility
        triangulationLocalFiniteness linkCompatibility plManifoldRecognition
        triangulationHomeomorphism moiseCompatibility triangulationUniqueness
        hauptvermutungDimensionThree plStructure plTransition plAtlas
        plManifoldAtlas plCollarNeighborhoodCompatibility
        plHomeomorphismCompatibility plAtlasMaximality plSmoothingExistence
        plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
        plSmoothingCompatibility plSmoothingUniqueness
        plSmoothingLocalModelCompatibility smoothStructure
        smoothAtlasConstruction smoothAtlasPLCompatibility
        smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
        smoothTransitionCompatibility smoothAtlasTransitionSmoothness :=
    HasSmoothStructureDerivation.ofOnePointRecognition
      (localCharts := localCharts)
      (locallyFiniteCoverRefinement := refinement)
      (simplicialComplex := simplicialComplex)
      (compatibleChartTriangulations := chartTriangulations)
      (triangulation := triangulation)
      (simplicialApproximation := simplicialApproximation)
      (starNeighborhoodBasis := starNeighborhoodBasis)
      (barycentricSubdivision := barycentricSubdivision)
      (regularNeighborhoodCompatibility := regularNeighborhoodCompatibility)
      (triangulationLocalFiniteness := triangulationLocalFiniteness)
      (linkCompatibility := linkCompatibility)
      (plManifoldRecognition := plManifoldRecognition)
      (triangulationHomeomorphism := triangulationHomeomorphism)
      (moiseCompatibility := moiseCompatibility)
      (triangulationUniqueness := triangulationUniqueness)
      (hauptvermutungDimensionThree := hauptvermutungDimensionThree)
      (plStructure := plStructure)
      (plTransitionCompatibility := plTransition)
      (plAtlas := plAtlas)
      (plManifoldAtlas := plManifoldAtlas)
      (plCollarNeighborhoodCompatibility := plCollarNeighborhoodCompatibility)
      (plHomeomorphismCompatibility := plHomeomorphismCompatibility)
      (plAtlasMaximality := plAtlasMaximality)
      (plSmoothingExistence := plSmoothingExistence)
      (plSmoothingObstructionVanishing := plSmoothingObstructionVanishing)
      (plMicrobundleSmoothing := plMicrobundleSmoothing)
      (smoothingTheorem := plSmoothing)
      (plSmoothingCompatibility := plSmoothingCompatibility)
      (plSmoothingUniqueness := plSmoothingUniqueness)
      (plSmoothingLocalModelCompatibility := plSmoothingLocalModelCompatibility)
      (smoothStructure := smoothStructure)
      (smoothAtlasConstruction := smoothAtlasConstruction)
      (smoothAtlasPLCompatibility := smoothAtlasPLCompatibility)
      (smoothAtlasMaximality := smoothAtlasMaximality)
      (smoothAtlasUniqueness := smoothAtlasUniqueness)
      (smoothStructureUniqueness := smoothStructureUniqueness)
      (smoothTransitionCompatibility := smoothTransitionCompatibility)
      (smoothAtlasTransitionSmoothness := smoothAtlasTransitionSmoothness)
      h rfl
  let smoothStructureDerivationStatement :
      SmoothStructureDerivationStatement M smoothStructure :=
    smooth_structure_derivation_statement_of_components M
      localCharts refinement simplicialComplex chartTriangulations
      triangulation simplicialApproximation starNeighborhoodBasis
      barycentricSubdivision regularNeighborhoodCompatibility
      triangulationLocalFiniteness linkCompatibility plManifoldRecognition
      triangulationHomeomorphism moiseCompatibility triangulationUniqueness
      hauptvermutungDimensionThree plStructure plTransition plAtlas
      plManifoldAtlas plCollarNeighborhoodCompatibility
      plHomeomorphismCompatibility plAtlasMaximality plSmoothingExistence
      plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
      plSmoothingCompatibility plSmoothingUniqueness
      plSmoothingLocalModelCompatibility smoothStructure
      smoothAtlasConstruction smoothAtlasPLCompatibility
      smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
      smoothTransitionCompatibility smoothAtlasTransitionSmoothness
      smoothStructureDerivation
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, smoothStructure,
      smoothStructureDerivationStatement, rfl⟩

/--
One-point recognition exposes the terminal smooth-structure derivation record
inside the `SmoothStructureDerivationStatement`, together with the recognition
payloads tying the statement and derivation back to the same one-point model.
-/
theorem smoothability_exists_smooth_structure_derivation_witness_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ smoothStructure : HasThreeManifoldSmoothStructure M,
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
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
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
    ∃ smoothStructureDerivation :
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
      SmoothStructureDerivationStatement M smoothStructure ∧
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) ∧
        smoothStructure =
          HasThreeManifoldSmoothStructure.ofOnePointRecognition
            smoothStructureDerivation.onePointRecognition ∧
        smoothStructure.onePointRecognition = h := by
  rcases
      smoothability_smooth_structure_derivation_statement_of_homeomorph_to_onePoint_threeSpace
        h with
    ⟨t2, charted, simple, compact, smooth, nonempty, smoothStructure,
      statement, smoothStructureRecognitionEq⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := smooth
  rcases statement with
    ⟨localCharts, refinement, simplicialComplex, chartTriangulations,
      triangulation, simplicialApproximation, starNeighborhoodBasis,
      barycentricSubdivision, regularNeighborhoodCompatibility,
      triangulationLocalFiniteness, linkCompatibility, plManifoldRecognition,
      triangulationHomeomorphism, moiseCompatibility, triangulationUniqueness,
      hauptvermutungDimensionThree, plStructure, plTransition, plAtlas,
      plManifoldAtlas, plCollarNeighborhoodCompatibility,
      plHomeomorphismCompatibility, plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality, smoothAtlasUniqueness,
      smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, smoothStructureDerivation⟩
  refine
    ⟨t2, charted, simple, compact, smooth, nonempty, smoothStructure,
      localCharts, refinement, simplicialComplex, chartTriangulations,
      triangulation, simplicialApproximation, starNeighborhoodBasis,
      barycentricSubdivision, regularNeighborhoodCompatibility,
      triangulationLocalFiniteness, linkCompatibility, plManifoldRecognition,
      triangulationHomeomorphism, moiseCompatibility, triangulationUniqueness,
      hauptvermutungDimensionThree, plStructure, plTransition, plAtlas,
      plManifoldAtlas, plCollarNeighborhoodCompatibility,
      plHomeomorphismCompatibility, plAtlasMaximality, plSmoothingExistence,
      plSmoothingObstructionVanishing, plMicrobundleSmoothing, plSmoothing,
      plSmoothingCompatibility, plSmoothingUniqueness,
      plSmoothingLocalModelCompatibility, smoothAtlasConstruction,
      smoothAtlasPLCompatibility, smoothAtlasMaximality,
      smoothAtlasUniqueness, smoothStructureUniqueness,
      smoothTransitionCompatibility, smoothAtlasTransitionSmoothness,
      smoothStructureDerivation, ?_, ?_, ?_, ?_⟩
  · exact smooth_structure_derivation_statement_of_components M
      localCharts refinement simplicialComplex chartTriangulations
      triangulation simplicialApproximation starNeighborhoodBasis
      barycentricSubdivision regularNeighborhoodCompatibility
      triangulationLocalFiniteness linkCompatibility plManifoldRecognition
      triangulationHomeomorphism moiseCompatibility triangulationUniqueness
      hauptvermutungDimensionThree plStructure plTransition plAtlas
      plManifoldAtlas plCollarNeighborhoodCompatibility
      plHomeomorphismCompatibility plAtlasMaximality plSmoothingExistence
      plSmoothingObstructionVanishing plMicrobundleSmoothing plSmoothing
      plSmoothingCompatibility plSmoothingUniqueness
      plSmoothingLocalModelCompatibility smoothStructure
      smoothAtlasConstruction smoothAtlasPLCompatibility
      smoothAtlasMaximality smoothAtlasUniqueness smoothStructureUniqueness
      smoothTransitionCompatibility smoothAtlasTransitionSmoothness
      smoothStructureDerivation
  · exact smoothStructureDerivation.onePointRecognition
  · exact smoothStructureDerivation.smoothStructure_eq
  · exact smoothStructureRecognitionEq

/--
One-point recognition exposes the smooth-atlas construction and transition
records as a smaller reusable payload, with every smooth-atlas and transition
witness tied back to the same recognition proof.
-/
theorem smoothability_smooth_atlas_transition_payload_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _nonempty : Nonempty M,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ plStructure : HasCompatiblePLStructure M triangulation,
    ∃ plAtlas : HasCompatiblePLAtlas M triangulation plStructure,
    ∃ plSmoothing : HasPLSmoothingTheorem M triangulation plStructure plAtlas,
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
    ∃ smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
    ∃ smoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility,
      smoothAtlasConstruction.onePointRecognition = h ∧
        smoothAtlasPLCompatibility.onePointRecognition = h ∧
        smoothAtlasMaximality.onePointRecognition = h ∧
        smoothTransitionCompatibility.onePointRecognition = h ∧
        smoothAtlasTransitionSmoothness.onePointRecognition = h ∧
        smoothStructure.onePointRecognition = h := by
  rcases
      smoothability_moise_to_smooth_atlas_core_of_homeomorph_to_onePoint_threeSpace
        h with
    ⟨t2, charted, simple, compact, smooth, nonempty, _localCharts,
      _refinement, _simplicialComplex, _chartTriangulations, triangulation,
      plStructure, plAtlas, plSmoothing, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, _smoothAtlasUniqueness,
      _smoothStructureUniqueness, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, _hlocal, _hrefinement, _hsimplicial,
      _hchartTriangulations, _htriangulation, _hplStructure, _hplAtlas,
      _hplSmoothing, hsmoothStructure, hsmoothAtlasConstruction,
      hsmoothAtlasPLCompatibility, hsmoothAtlasMaximality,
      _hsmoothAtlasUniqueness, _hsmoothStructureUniqueness,
      hsmoothTransitionCompatibility, hsmoothAtlasTransitionSmoothness⟩
  exact
    ⟨t2, charted, simple, compact, smooth, nonempty, triangulation,
      plStructure, plAtlas, plSmoothing, smoothStructure,
      smoothAtlasConstruction, smoothAtlasPLCompatibility,
      smoothAtlasMaximality, smoothTransitionCompatibility,
      smoothAtlasTransitionSmoothness, hsmoothAtlasConstruction,
      hsmoothAtlasPLCompatibility, hsmoothAtlasMaximality,
      hsmoothTransitionCompatibility, hsmoothAtlasTransitionSmoothness,
      hsmoothStructure⟩

/--
**Step 3701 source.** One-point recognition now supplies a joint
smoothability endpoint: a full `SmoothStructureDerivationStatement` and an
independently exposed smooth-atlas transition payload, with the smooth
structures and transition witnesses all verified against the same recognition
homeomorphism.  This packages the Moise-to-smoothing derivation used in the
smoothability section with the concrete smooth-atlas transition witnesses from
the one-point compactification recognition route.
-/
theorem smoothability_onePoint_smooth_atlas_transition_derivation_bundle_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _derivationT2 : T2Space M,
    ∃ _derivationCharted : ChartedSpace ThreeManifoldModel M,
    ∃ _derivationSimple : SimplyConnectedSpace M,
    ∃ _derivationCompact : CompactSpace M,
    ∃ _derivationSmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _derivationNonempty : Nonempty M,
    ∃ derivationSmoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ _derivationStatement :
      SmoothStructureDerivationStatement M derivationSmoothStructure,
    ∃ derivationRecognition :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))),
      derivationRecognition =
        derivationSmoothStructure.onePointRecognition ∧
        derivationRecognition = h ∧
    ∃ _payloadT2 : T2Space M,
    ∃ _payloadCharted : ChartedSpace ThreeManifoldModel M,
    ∃ _payloadSimple : SimplyConnectedSpace M,
    ∃ _payloadCompact : CompactSpace M,
    ∃ _payloadSmooth : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ _payloadNonempty : Nonempty M,
    ∃ payloadTriangulation : HasMoiseTriangulation M,
    ∃ payloadPLStructure :
      HasCompatiblePLStructure M payloadTriangulation,
    ∃ payloadPLAtlas :
      HasCompatiblePLAtlas M payloadTriangulation payloadPLStructure,
    ∃ payloadPLSmoothing :
      HasPLSmoothingTheorem
        M payloadTriangulation payloadPLStructure payloadPLAtlas,
    ∃ payloadSmoothStructure : HasThreeManifoldSmoothStructure M,
    ∃ payloadSmoothAtlasConstruction :
      HasSmoothAtlasConstruction
        M payloadTriangulation payloadPLStructure payloadPLAtlas
        payloadPLSmoothing payloadSmoothStructure,
    ∃ payloadSmoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M payloadTriangulation payloadPLStructure payloadPLAtlas
        payloadPLSmoothing payloadSmoothStructure
        payloadSmoothAtlasConstruction,
    ∃ payloadSmoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M payloadTriangulation payloadPLStructure payloadPLAtlas
        payloadPLSmoothing payloadSmoothStructure,
    ∃ payloadSmoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M payloadSmoothStructure,
    ∃ payloadSmoothAtlasTransitionSmoothness :
      HasSmoothAtlasTransitionSmoothness
        M payloadSmoothStructure payloadSmoothTransitionCompatibility,
      payloadSmoothAtlasConstruction.onePointRecognition = h ∧
        payloadSmoothAtlasPLCompatibility.onePointRecognition = h ∧
        payloadSmoothAtlasMaximality.onePointRecognition = h ∧
        payloadSmoothTransitionCompatibility.onePointRecognition = h ∧
        payloadSmoothAtlasTransitionSmoothness.onePointRecognition = h ∧
        payloadSmoothStructure.onePointRecognition = h ∧
        derivationRecognition =
          payloadSmoothStructure.onePointRecognition := by
  rcases
      smoothability_smooth_structure_derivation_statement_of_homeomorph_to_onePoint_threeSpace
        h with
    ⟨derivationT2, derivationCharted, derivationSimple,
      derivationCompact, derivationSmooth, derivationNonempty,
      derivationSmoothStructure, derivationStatement,
      hDerivationSmoothStructure⟩
  let derivationRecognition :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :=
    derivationSmoothStructure.onePointRecognition
  have hDerivationRecognitionField :
      derivationRecognition =
        derivationSmoothStructure.onePointRecognition := rfl
  have hDerivationRecognition : derivationRecognition = h :=
    hDerivationSmoothStructure
  rcases
      smoothability_smooth_atlas_transition_payload_of_homeomorph_to_onePoint_threeSpace
        h with
    ⟨payloadT2, payloadCharted, payloadSimple, payloadCompact,
      payloadSmooth, payloadNonempty, payloadTriangulation,
      payloadPLStructure, payloadPLAtlas, payloadPLSmoothing,
      payloadSmoothStructure, payloadSmoothAtlasConstruction,
      payloadSmoothAtlasPLCompatibility, payloadSmoothAtlasMaximality,
      payloadSmoothTransitionCompatibility, payloadSmoothAtlasTransitionSmoothness,
      hPayloadSmoothAtlasConstruction, hPayloadSmoothAtlasPLCompatibility,
      hPayloadSmoothAtlasMaximality, hPayloadSmoothTransitionCompatibility,
      hPayloadSmoothAtlasTransitionSmoothness, hPayloadSmoothStructure⟩
  refine
    ⟨derivationT2, derivationCharted, derivationSimple,
      derivationCompact, derivationSmooth, derivationNonempty,
      derivationSmoothStructure, derivationStatement,
      derivationRecognition, hDerivationRecognitionField,
      hDerivationRecognition, payloadT2, payloadCharted,
      payloadSimple, payloadCompact, payloadSmooth,
      payloadNonempty, payloadTriangulation, payloadPLStructure,
      payloadPLAtlas, payloadPLSmoothing, payloadSmoothStructure,
      payloadSmoothAtlasConstruction, payloadSmoothAtlasPLCompatibility,
      payloadSmoothAtlasMaximality, payloadSmoothTransitionCompatibility,
      payloadSmoothAtlasTransitionSmoothness,
      hPayloadSmoothAtlasConstruction, hPayloadSmoothAtlasPLCompatibility,
      hPayloadSmoothAtlasMaximality, hPayloadSmoothTransitionCompatibility,
      hPayloadSmoothAtlasTransitionSmoothness, hPayloadSmoothStructure, ?_⟩
  exact hDerivationRecognition.trans hPayloadSmoothStructure.symm

end Poincare
