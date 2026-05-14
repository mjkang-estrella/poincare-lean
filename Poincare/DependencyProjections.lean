/-
Projection lemmas for the aggregate dependency package.

These lemmas do not construct the missing dependencies. They make the exact
outputs of a completed `PoincareProofDependencies` package available as named
Lean theorems, so later work can replace individual fields without disturbing
the final assembly theorem.
-/

import Poincare.Dependencies

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- A completed dependency package supplies the smoothability package. -/
theorem smoothability_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    SmoothabilityPackage.{u} :=
  dependencies.smoothability

/-- The dependency-level smoothability projection is the stored field. -/
theorem smoothability_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_package_of_dependencies dependencies =
      dependencies.smoothability :=
  rfl

/--
The legacy dependency-projection name agrees with the structural aggregate
smoothability projection.
-/
theorem smoothability_package_of_dependencies_to_structural_projection_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_package_of_dependencies dependencies =
      smoothability_of_poincareProofDependencies dependencies :=
  rfl

/-- A completed dependency package supplies Moise triangulation evidence. -/
theorem smoothability_moise_local_charts_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocalTriangulationCharts M :=
  moise_local_charts_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies locally finite chart refinement. -/
theorem smoothability_moise_locally_finite_cover_refinement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLocallyFiniteCoverRefinement M
      (smoothability_moise_local_charts_of_dependencies dependencies M) :=
  moise_locally_finite_cover_refinement_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies Moise simplicial-complex evidence. -/
theorem smoothability_moise_simplicial_complex_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialComplex M
      (smoothability_moise_local_charts_of_dependencies dependencies M) :=
  moise_simplicial_complex_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies compatible local chart triangulations. -/
theorem smoothability_moise_compatible_chart_triangulations_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseCompatibleChartTriangulations M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_simplicial_complex_of_dependencies dependencies M) :=
  moise_compatible_chart_triangulations_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies Moise triangulation evidence. -/
theorem smoothability_moise_triangulation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulation M :=
  moise_triangulation_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies simplicial approximation evidence. -/
theorem smoothability_moise_simplicial_approximation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseSimplicialApproximation M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_simplicial_complex_of_dependencies dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_simplicial_approximation_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies a Moise star-neighborhood basis. -/
theorem smoothability_moise_star_neighborhood_basis_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseStarNeighborhoodBasis M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_star_neighborhood_basis_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies barycentric subdivision control. -/
theorem smoothability_moise_barycentric_subdivision_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseBarycentricSubdivisionControl M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_barycentric_subdivision_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies regular-neighborhood compatibility. -/
theorem smoothability_moise_regular_neighborhood_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseRegularNeighborhoodCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_regular_neighborhood_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies local-finiteness evidence. -/
theorem smoothability_moise_triangulation_local_finiteness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationLocalFiniteness M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_triangulation_local_finiteness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies the Moise link condition. -/
theorem smoothability_moise_link_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseLinkCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_link_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package recognizes the Moise triangulation as a PL manifold. -/
theorem smoothability_moise_pl_manifold_recognition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoisePLManifoldRecognition M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_moise_link_compatibility_of_dependencies dependencies M) :=
  moise_pl_manifold_recognition_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies the Moise triangulation homeomorphism. -/
theorem smoothability_moise_triangulation_homeomorphism_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationHomeomorphism M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_triangulation_homeomorphism_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies Moise compatibility evidence. -/
theorem smoothability_moise_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationCompatibility M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies Moise triangulation uniqueness. -/
theorem smoothability_moise_triangulation_uniqueness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseTriangulationUniqueness M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  moise_triangulation_uniqueness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies the dimension-three Hauptvermutung input. -/
theorem smoothability_moise_hauptvermutung_dimension_three_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasMoiseHauptvermutungDimensionThree M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_moise_triangulation_uniqueness_of_dependencies dependencies M) :=
  moise_hauptvermutung_dimension_three_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies compatible PL-structure evidence. -/
theorem smoothability_pl_structure_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLStructure M
      (smoothability_moise_triangulation_of_dependencies dependencies M) :=
  pl_structure_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL transition compatibility. -/
theorem smoothability_pl_transition_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLTransitionCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M) :=
  pl_transition_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies compatible PL-atlas evidence. -/
theorem smoothability_pl_atlas_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasCompatiblePLAtlas M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M) :=
  pl_atlas_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL-manifold atlas evidence. -/
theorem smoothability_pl_manifold_atlas_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLManifoldAtlas M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_manifold_atlas_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL collar-neighborhood compatibility. -/
theorem smoothability_pl_collar_neighborhood_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLCollarNeighborhoodCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_collar_neighborhood_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies Moise-homeomorphism/PL compatibility. -/
theorem smoothability_pl_homeomorphism_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLHomeomorphismCompatibility M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_homeomorphism_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL atlas maximality. -/
theorem smoothability_pl_atlas_maximality_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLAtlasMaximality M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_atlas_maximality_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL smoothing existence. -/
theorem smoothability_pl_smoothing_existence_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingExistence M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_smoothing_existence_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL-smoothing obstruction vanishing. -/
theorem smoothability_pl_smoothing_obstruction_vanishing_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingObstructionVanishing M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_smoothing_obstruction_vanishing_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL microbundle smoothing evidence. -/
theorem smoothability_pl_microbundle_smoothing_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLMicrobundleSmoothing M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_existence_of_dependencies dependencies M)
      (smoothability_pl_smoothing_obstruction_vanishing_of_dependencies
        dependencies M) :=
  pl_microbundle_smoothing_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies the PL smoothing theorem input. -/
theorem smoothability_pl_smoothing_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingTheorem M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M) :=
  pl_smoothing_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL smoothing compatibility. -/
theorem smoothability_pl_smoothing_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M) :=
  pl_smoothing_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL smoothing uniqueness. -/
theorem smoothability_pl_smoothing_uniqueness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingUniqueness M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M) :=
  pl_smoothing_uniqueness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies PL-smoothing local-model compatibility. -/
theorem smoothability_pl_smoothing_local_model_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasPLSmoothingLocalModelCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M) :=
  pl_smoothing_local_model_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth atlas construction evidence. -/
theorem smoothability_smooth_atlas_construction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasConstruction M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M)
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_atlas_construction_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth-atlas/PL-atlas compatibility. -/
theorem smoothability_smooth_atlas_pl_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasPLCompatibility M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M)
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_atlas_pl_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth atlas maximality. -/
theorem smoothability_smooth_atlas_maximality_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasMaximality M
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M)
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_atlas_maximality_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth atlas uniqueness evidence. -/
theorem smoothability_smooth_atlas_uniqueness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasUniqueness M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_atlas_uniqueness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth-structure uniqueness evidence. -/
theorem smoothability_smooth_structure_uniqueness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureUniquenessUpToDiffeomorphism M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_structure_uniqueness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth transition compatibility. -/
theorem smoothability_smooth_transition_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothTransitionCompatibility M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) :=
  smooth_transition_compatibility_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- A completed dependency package supplies smooth transition-map smoothness. -/
theorem smoothability_smooth_atlas_transition_smoothness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothAtlasTransitionSmoothness M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M)
      (smoothability_smooth_transition_compatibility_of_dependencies dependencies M) :=
  smooth_atlas_transition_smoothness_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/--
A completed dependency package supplies the derivation from triangulation and
PL structure to the smooth-structure input.
-/
theorem smoothability_smooth_structure_derivation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothStructureDerivation M
      (smoothability_moise_local_charts_of_dependencies dependencies M)
      (smoothability_moise_locally_finite_cover_refinement_of_dependencies
        dependencies M)
      (smoothability_moise_simplicial_complex_of_dependencies dependencies M)
      (smoothability_moise_compatible_chart_triangulations_of_dependencies
        dependencies M)
      (smoothability_moise_triangulation_of_dependencies dependencies M)
      (smoothability_moise_simplicial_approximation_of_dependencies
        dependencies M)
      (smoothability_moise_star_neighborhood_basis_of_dependencies
        dependencies M)
      (smoothability_moise_barycentric_subdivision_of_dependencies
        dependencies M)
      (smoothability_moise_regular_neighborhood_compatibility_of_dependencies
        dependencies M)
      (smoothability_moise_triangulation_local_finiteness_of_dependencies
        dependencies M)
      (smoothability_moise_link_compatibility_of_dependencies dependencies M)
      (smoothability_moise_pl_manifold_recognition_of_dependencies
        dependencies M)
      (smoothability_moise_triangulation_homeomorphism_of_dependencies
        dependencies M)
      (smoothability_moise_compatibility_of_dependencies dependencies M)
      (smoothability_moise_triangulation_uniqueness_of_dependencies
        dependencies M)
      (smoothability_moise_hauptvermutung_dimension_three_of_dependencies
        dependencies M)
      (smoothability_pl_structure_of_dependencies dependencies M)
      (smoothability_pl_transition_compatibility_of_dependencies dependencies M)
      (smoothability_pl_atlas_of_dependencies dependencies M)
      (smoothability_pl_manifold_atlas_of_dependencies dependencies M)
      (smoothability_pl_collar_neighborhood_compatibility_of_dependencies
        dependencies M)
      (smoothability_pl_homeomorphism_compatibility_of_dependencies
        dependencies M)
      (smoothability_pl_atlas_maximality_of_dependencies dependencies M)
      (smoothability_pl_smoothing_existence_of_dependencies dependencies M)
      (smoothability_pl_smoothing_obstruction_vanishing_of_dependencies
        dependencies M)
      (smoothability_pl_microbundle_smoothing_of_dependencies dependencies M)
      (smoothability_pl_smoothing_of_dependencies dependencies M)
      (smoothability_pl_smoothing_compatibility_of_dependencies dependencies M)
      (smoothability_pl_smoothing_uniqueness_of_dependencies dependencies M)
      (smoothability_pl_smoothing_local_model_compatibility_of_dependencies
        dependencies M)
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M)
      (smoothability_smooth_atlas_construction_of_dependencies dependencies M)
      (smoothability_smooth_atlas_pl_compatibility_of_dependencies dependencies M)
      (smoothability_smooth_atlas_maximality_of_dependencies dependencies M)
      (smoothability_smooth_atlas_uniqueness_of_dependencies dependencies M)
      (smoothability_smooth_structure_uniqueness_of_dependencies dependencies M)
      (smoothability_smooth_transition_compatibility_of_dependencies
        dependencies M)
      (smoothability_smooth_atlas_transition_smoothness_of_dependencies
        dependencies M) :=
  smooth_structure_derivation_of_smoothability_package
    (smoothability_package_of_dependencies dependencies) M

/-- The dependency-level Moise local-chart projection is the stored smoothability field. -/
theorem smoothability_moise_local_charts_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_local_charts_of_dependencies dependencies M =
      moise_local_charts_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Moise triangulation projection is the stored smoothability field. -/
theorem smoothability_moise_triangulation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_triangulation_of_dependencies dependencies M =
      moise_triangulation_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-structure projection is the stored smoothability field. -/
theorem smoothability_pl_structure_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_structure_of_dependencies dependencies M =
      pl_structure_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-atlas projection is the stored smoothability field. -/
theorem smoothability_pl_atlas_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_atlas_of_dependencies dependencies M =
      pl_atlas_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing projection is the stored smoothability field. -/
theorem smoothability_pl_smoothing_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_of_dependencies dependencies M =
      pl_smoothing_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-atlas construction projection is the stored field. -/
theorem smoothability_smooth_atlas_construction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_atlas_construction_of_dependencies dependencies M =
      smooth_atlas_construction_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-transition projection is the stored field. -/
theorem smoothability_smooth_transition_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_transition_compatibility_of_dependencies dependencies M =
      smooth_transition_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth transition-map projection is the stored field. -/
theorem smoothability_smooth_atlas_transition_smoothness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_atlas_transition_smoothness_of_dependencies
        dependencies M =
      smooth_atlas_transition_smoothness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-structure derivation projection is the stored field. -/
theorem smoothability_smooth_structure_derivation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_derivation_of_dependencies dependencies M =
      smooth_structure_derivation_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level locally finite chart-refinement projection is the stored field. -/
theorem smoothability_moise_locally_finite_cover_refinement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_locally_finite_cover_refinement_of_dependencies
        dependencies M =
      moise_locally_finite_cover_refinement_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Moise simplicial-complex projection is the stored field. -/
theorem smoothability_moise_simplicial_complex_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_simplicial_complex_of_dependencies dependencies M =
      moise_simplicial_complex_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level compatible chart-triangulation projection is the stored field. -/
theorem smoothability_moise_compatible_chart_triangulations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_compatible_chart_triangulations_of_dependencies
        dependencies M =
      moise_compatible_chart_triangulations_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level simplicial-approximation projection is the stored field. -/
theorem smoothability_moise_simplicial_approximation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_simplicial_approximation_of_dependencies dependencies M =
      moise_simplicial_approximation_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level star-neighborhood basis projection is the stored field. -/
theorem smoothability_moise_star_neighborhood_basis_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_star_neighborhood_basis_of_dependencies dependencies M =
      moise_star_neighborhood_basis_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level barycentric-subdivision projection is the stored field. -/
theorem smoothability_moise_barycentric_subdivision_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_barycentric_subdivision_of_dependencies dependencies M =
      moise_barycentric_subdivision_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level regular-neighborhood projection is the stored field. -/
theorem smoothability_moise_regular_neighborhood_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_regular_neighborhood_compatibility_of_dependencies
        dependencies M =
      moise_regular_neighborhood_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level triangulation local-finiteness projection is the stored field. -/
theorem smoothability_moise_triangulation_local_finiteness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_triangulation_local_finiteness_of_dependencies
        dependencies M =
      moise_triangulation_local_finiteness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Moise link-compatibility projection is the stored field. -/
theorem smoothability_moise_link_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_link_compatibility_of_dependencies dependencies M =
      moise_link_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-manifold recognition projection is the stored field. -/
theorem smoothability_moise_pl_manifold_recognition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_pl_manifold_recognition_of_dependencies dependencies M =
      moise_pl_manifold_recognition_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level triangulation-homeomorphism projection is the stored field. -/
theorem smoothability_moise_triangulation_homeomorphism_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_triangulation_homeomorphism_of_dependencies
        dependencies M =
      moise_triangulation_homeomorphism_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Moise compatibility projection is the stored field. -/
theorem smoothability_moise_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_compatibility_of_dependencies dependencies M =
      moise_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Moise triangulation-uniqueness projection is the stored field. -/
theorem smoothability_moise_triangulation_uniqueness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_triangulation_uniqueness_of_dependencies dependencies M =
      moise_triangulation_uniqueness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level Hauptvermutung input projection is the stored field. -/
theorem smoothability_moise_hauptvermutung_dimension_three_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_moise_hauptvermutung_dimension_three_of_dependencies
        dependencies M =
      moise_hauptvermutung_dimension_three_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-transition projection is the stored field. -/
theorem smoothability_pl_transition_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_transition_compatibility_of_dependencies dependencies M =
      pl_transition_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-manifold atlas projection is the stored field. -/
theorem smoothability_pl_manifold_atlas_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_manifold_atlas_of_dependencies dependencies M =
      pl_manifold_atlas_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level PL collar-neighborhood projection is the stored field. -/
theorem smoothability_pl_collar_neighborhood_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_collar_neighborhood_compatibility_of_dependencies
        dependencies M =
      pl_collar_neighborhood_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL homeomorphism-compatibility projection is the stored field. -/
theorem smoothability_pl_homeomorphism_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_homeomorphism_compatibility_of_dependencies dependencies M =
      pl_homeomorphism_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-atlas maximality projection is the stored field. -/
theorem smoothability_pl_atlas_maximality_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_atlas_maximality_of_dependencies dependencies M =
      pl_atlas_maximality_of_smoothability_package dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing existence projection is the stored field. -/
theorem smoothability_pl_smoothing_existence_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_existence_of_dependencies dependencies M =
      pl_smoothing_existence_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing obstruction projection is the stored field. -/
theorem smoothability_pl_smoothing_obstruction_vanishing_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_obstruction_vanishing_of_dependencies
        dependencies M =
      pl_smoothing_obstruction_vanishing_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL microbundle-smoothing projection is the stored field. -/
theorem smoothability_pl_microbundle_smoothing_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_microbundle_smoothing_of_dependencies dependencies M =
      pl_microbundle_smoothing_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing compatibility projection is the stored field. -/
theorem smoothability_pl_smoothing_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_compatibility_of_dependencies dependencies M =
      pl_smoothing_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing uniqueness projection is the stored field. -/
theorem smoothability_pl_smoothing_uniqueness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_uniqueness_of_dependencies dependencies M =
      pl_smoothing_uniqueness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level PL-smoothing local-model projection is the stored field. -/
theorem smoothability_pl_smoothing_local_model_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_pl_smoothing_local_model_compatibility_of_dependencies
        dependencies M =
      pl_smoothing_local_model_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-atlas/PL compatibility projection is the stored field. -/
theorem smoothability_smooth_atlas_pl_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_atlas_pl_compatibility_of_dependencies dependencies M =
      smooth_atlas_pl_compatibility_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-atlas maximality projection is the stored field. -/
theorem smoothability_smooth_atlas_maximality_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_atlas_maximality_of_dependencies dependencies M =
      smooth_atlas_maximality_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-atlas uniqueness projection is the stored field. -/
theorem smoothability_smooth_atlas_uniqueness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_atlas_uniqueness_of_dependencies dependencies M =
      smooth_atlas_uniqueness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/-- The dependency-level smooth-structure uniqueness projection is the stored field. -/
theorem smoothability_smooth_structure_uniqueness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_uniqueness_of_dependencies dependencies M =
      smooth_structure_uniqueness_of_smoothability_package
        dependencies.smoothability M :=
  rfl

/--
A completed dependency package exposes the smooth-structure derivation payload:
the component-level derivation certificate together with the theorem-shaped
smooth-structure derivation statement.
-/
theorem smoothability_smooth_structure_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ _smoothDerivation :
      HasSmoothStructureDerivation M
        (smoothability_moise_local_charts_of_dependencies dependencies M)
        (smoothability_moise_locally_finite_cover_refinement_of_dependencies
          dependencies M)
        (smoothability_moise_simplicial_complex_of_dependencies dependencies M)
        (smoothability_moise_compatible_chart_triangulations_of_dependencies
          dependencies M)
        (smoothability_moise_triangulation_of_dependencies dependencies M)
        (smoothability_moise_simplicial_approximation_of_dependencies
          dependencies M)
        (smoothability_moise_star_neighborhood_basis_of_dependencies
          dependencies M)
        (smoothability_moise_barycentric_subdivision_of_dependencies
          dependencies M)
        (smoothability_moise_regular_neighborhood_compatibility_of_dependencies
          dependencies M)
        (smoothability_moise_triangulation_local_finiteness_of_dependencies
          dependencies M)
        (smoothability_moise_link_compatibility_of_dependencies dependencies M)
        (smoothability_moise_pl_manifold_recognition_of_dependencies
          dependencies M)
        (smoothability_moise_triangulation_homeomorphism_of_dependencies
          dependencies M)
        (smoothability_moise_compatibility_of_dependencies dependencies M)
        (smoothability_moise_triangulation_uniqueness_of_dependencies
          dependencies M)
        (smoothability_moise_hauptvermutung_dimension_three_of_dependencies
          dependencies M)
        (smoothability_pl_structure_of_dependencies dependencies M)
        (smoothability_pl_transition_compatibility_of_dependencies
          dependencies M)
        (smoothability_pl_atlas_of_dependencies dependencies M)
        (smoothability_pl_manifold_atlas_of_dependencies dependencies M)
        (smoothability_pl_collar_neighborhood_compatibility_of_dependencies
          dependencies M)
        (smoothability_pl_homeomorphism_compatibility_of_dependencies
          dependencies M)
        (smoothability_pl_atlas_maximality_of_dependencies dependencies M)
        (smoothability_pl_smoothing_existence_of_dependencies dependencies M)
        (smoothability_pl_smoothing_obstruction_vanishing_of_dependencies
          dependencies M)
        (smoothability_pl_microbundle_smoothing_of_dependencies dependencies M)
        (smoothability_pl_smoothing_of_dependencies dependencies M)
        (smoothability_pl_smoothing_compatibility_of_dependencies
          dependencies M)
        (smoothability_pl_smoothing_uniqueness_of_dependencies dependencies M)
        (smoothability_pl_smoothing_local_model_compatibility_of_dependencies
          dependencies M)
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M)
        (smoothability_smooth_atlas_construction_of_dependencies
          dependencies M)
        (smoothability_smooth_atlas_pl_compatibility_of_dependencies
          dependencies M)
        (smoothability_smooth_atlas_maximality_of_dependencies dependencies M)
        (smoothability_smooth_atlas_uniqueness_of_dependencies dependencies M)
        (smoothability_smooth_structure_uniqueness_of_dependencies
          dependencies M)
        (smoothability_smooth_transition_compatibility_of_dependencies
          dependencies M)
        (smoothability_smooth_atlas_transition_smoothness_of_dependencies
          dependencies M),
      SmoothStructureDerivationStatement M
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M) := by
  rcases
      smoothability_smooth_structure_statement_payload_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M with
    ⟨smoothDerivation, derivationStatement⟩
  exact ⟨smoothDerivation, derivationStatement⟩

/--
A completed dependency package supplies the packaged smooth-structure
derivation statement.
-/
theorem smoothability_smooth_structure_derivation_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothStructureDerivationStatement M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M) := by
  rcases smoothability_smooth_structure_statement_payload_of_dependencies
      dependencies M with
    ⟨_smoothDerivation, derivationStatement⟩
  exact derivationStatement

/--
The dependency-level smooth-structure statement payload is the corresponding
payload of the stored smoothability package.
-/
theorem smoothability_smooth_structure_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_statement_payload_of_dependencies
      dependencies M =
      smoothability_smooth_structure_statement_payload_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
The dependency-level smooth-structure derivation statement is the corresponding
projection of the stored smoothability package.
-/
theorem smoothability_smooth_structure_derivation_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_smooth_structure_derivation_statement_of_dependencies
      dependencies M =
      smooth_structure_derivation_statement_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
A completed dependency package supplies finite-extinction surgery packages for
all target manifolds after the smoothability regularity has been installed.
-/
theorem surgery_packages_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  dependencies.surgery

/-- The dependency-level surgery-package-family projection is the stored field. -/
theorem surgery_packages_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_packages_of_dependencies dependencies = dependencies.surgery :=
  rfl

/--
The legacy dependency-projection name agrees with the structural aggregate
surgery-family projection.
-/
theorem surgery_packages_of_dependencies_to_structural_projection_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_packages_of_dependencies dependencies =
      surgery_of_poincareProofDependencies dependencies :=
  rfl

/--
The strengthened dependency package supplies boundary-carrying surgery
packages for every target manifold after smoothability regularity has been
installed.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty
          (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :=
  dependencies.surgery

/--
The strengthened dependency-level boundary-carrying surgery package projection
is the stored field.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_packages_with_equation_boundary_of_dependencies dependencies =
      dependencies.surgery :=
  rfl

/--
The legacy strengthened dependency-projection name agrees with the structural
boundary-carrying surgery-family projection.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_to_structural_projection_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_packages_with_equation_boundary_of_dependencies dependencies =
      surgery_of_poincareProofDependenciesWithEquationBoundary dependencies :=
  rfl

/--
Forgetting equation boundaries from strengthened dependencies supplies the
ordinary finite-extinction surgery package family.
-/
theorem surgery_packages_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  surgery_packages_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The ordinary surgery-package projection from strengthened dependencies is the
ordinary projection applied to the forgetful aggregate dependency package.
-/
theorem surgery_packages_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_packages_of_equation_boundary_dependencies dependencies =
      surgery_packages_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) :=
  rfl

/--
The ordinary surgery projection from strengthened dependencies also agrees
with the structural surgery projection after applying the forgetful aggregate
dependency map.
-/
theorem surgery_packages_of_equation_boundary_dependencies_to_structural_projection_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_packages_of_equation_boundary_dependencies dependencies =
      surgery_of_poincareProofDependencies
        (dependencies_of_equation_boundary_dependencies dependencies) :=
  rfl

/--
Strengthened dependencies expose explicit Ricci-flow equation-boundary
packages for the projected surgery flows.
-/
theorem ricci_flow_equation_boundary_packages_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          Nonempty
            (RicciFlowEquationBoundaryPackage
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))) := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨n, package,
      ⟨equation_boundary_of_surgery_package_with_equation_boundary package⟩⟩

/--
The strengthened dependency equation-boundary package projection is selected
from the stored boundary-carrying surgery package family.
-/
theorem ricci_flow_equation_boundary_packages_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ricci_flow_equation_boundary_packages_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            ⟨equation_boundary_of_surgery_package_with_equation_boundary
              package⟩⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the full projection-routed equation-boundary
derivative payload carried by the selected surgery package: equation
verification, metric-derivative data, derivative identification, and the
pointwise Ricci-flow equation.
-/
theorem equation_boundary_derivative_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ verification :
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _verification_eq :
          verification =
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
        ∃ metricDerivative :
          MetricTimeDerivativeData
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _metricDerivative_eq :
          metricDerivative =
            metric_derivative_data_of_surgery_package_with_equation_boundary
              package,
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package)))
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) ∧
          ∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                metricDerivative) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  let verification :=
    ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
      package
  let metricDerivative :=
    metric_derivative_data_of_surgery_package_with_equation_boundary package
  exact
    ⟨n, package, verification, rfl, metricDerivative, rfl,
      metric_time_derivative_identification_of_surgery_package_with_equation_boundary
        package,
      equation_at_time_of_surgery_package_with_equation_boundary_projection
        package⟩

/--
The strengthened dependency equation-boundary derivative payload is selected
from the stored boundary-carrying surgery package family.
-/
theorem equation_boundary_derivative_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_derivative_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        let verification :=
          ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
            package
        let metricDerivative :=
          metric_derivative_data_of_surgery_package_with_equation_boundary
            package
        exact
          ⟨n, package, verification, rfl, metricDerivative, rfl,
            metric_time_derivative_identification_of_surgery_package_with_equation_boundary
              package,
            equation_at_time_of_surgery_package_with_equation_boundary_projection
              package⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the projection-routed equation-boundary
equation pointwise through their selected surgery package.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          ∀ (t : ℝ) (x : M)
            (v w : TangentSpace ThreeManifoldModelWithCorners x),
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_surgery_package_with_equation_boundary
                  package)) t x v w =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t x v w := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨n, package,
      equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
        package⟩

/--
The dependency pointwise equation payload is selected from the stored
boundary-carrying surgery package family.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_pointwise_equation_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
              package⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the direct stored-verification pointwise
equation payload for each selected boundary-carrying surgery package.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload
            package := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨n, package,
      surgery_package_with_equation_boundary_direct_pointwise_equation_payload
        package⟩

/--
The dependency direct pointwise equation payload is selected from the stored
boundary-carrying surgery package family.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_direct_pointwise_equation_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_direct_pointwise_equation_payload
              package⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the full derivative-strengthened surgery
payload selected from their boundary-carrying surgery package family.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryDerivativePayload package := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨n, package,
      surgery_package_with_equation_boundary_derivative_payload package⟩

/--
The dependency-level full surgery derivative payload is selected from the
stored boundary-carrying surgery package family and then routed through the
package-level derivative payload theorem.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_derivative_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_derivative_payload
              package⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the scalar-pointwise surgery payload selected
from their boundary-carrying surgery package family.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact
    ⟨n, package,
      surgery_package_with_equation_boundary_pointwise_equation_payload
        package⟩

/--
The dependency-level scalar-pointwise surgery payload is selected from the
stored boundary-carrying surgery package family and then routed through the
package-level pointwise payload theorem.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_pointwise_equation_payload
              package⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the boundary-carrying surgery package payload
selected from their boundary-carrying surgery package family.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
        ∃ _equationBoundary :
          RicciFlowEquationBoundaryPackage
            (ricci_flow_data_of_surgery_package basePackage),
        ∃ _analyticBoundary :
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package basePackage),
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  exact ⟨n, package, surgery_package_with_equation_boundary_payload package⟩

/--
The dependency-level boundary package payload is selected from the stored
boundary-carrying surgery package family.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_payload package⟩) := by
  apply Subsingleton.elim

/--
The dependency-level boundary package payload is the forgetful projection of
the full derivative-strengthened surgery payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies_to_surgery_derivative_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_dependencies
              dependencies M with
          ⟨n, package, _basePackage, _basePackage_eq, equationBoundary,
            _verification, _verification_eq, _metricDerivative,
            _metricDerivative_eq, _derivativeId, _equationAtTime,
            analyticBoundary, finiteExtinction⟩
        exact
          ⟨n, package,
            surgery_package_of_equation_boundary_surgery_package package,
            equationBoundary, analyticBoundary, finiteExtinction⟩) := by
  apply Subsingleton.elim

/--
The dependency-level boundary package payload is the forgetful projection of the
package-level scalar-pointwise surgery payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies_to_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
The dependency-level boundary package payload is reconstructed from the
dependency-level direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
The older dependency-level equation/metric derivative payload is the forgetful
projection of the full derivative-strengthened surgery payload.
-/
theorem equation_boundary_derivative_payload_of_dependencies_to_surgery_derivative_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_derivative_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_dependencies
              dependencies M with
          ⟨n, package, _basePackage, _basePackage_eq, _equationBoundary,
            verification, verification_eq, metricDerivative,
            metricDerivative_eq, derivativeId, equationAtTime,
            _analyticBoundary, _finiteExtinction⟩
        exact
          ⟨n, package, verification, verification_eq, metricDerivative,
            metricDerivative_eq, derivativeId, equationAtTime⟩) := by
  apply Subsingleton.elim

/--
The dependency-level pointwise equation payload is the pointwise projection of
the full derivative-strengthened surgery payload.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies_to_surgery_derivative_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_pointwise_equation_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_dependencies
              dependencies M with
          ⟨n, package, _basePackage, _basePackage_eq, _equationBoundary,
            _verification, _verification_eq, metricDerivative,
            metricDerivative_eq, _derivativeId, equationAtTime,
            _analyticBoundary, _finiteExtinction⟩
        exact
          ⟨n, package, by
            intro t x v w
            rw [← metricDerivative_eq]
            exact congrArg (fun tensor => tensor x v w)
              (equationAtTime t)⟩) := by
  apply Subsingleton.elim

/--
The dependency-level pointwise equation payload is the scalar-equation projection
of the full package-level pointwise surgery payload.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies_to_surgery_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_pointwise_equation_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, pointwisePayload⟩
        rcases pointwisePayload with
          ⟨_basePackage, _basePackage_eq, _equationBoundary,
            _verification, _verification_eq, metricDerivative,
            metricDerivative_eq, _derivativeId, pointwiseEquation,
            _analyticBoundary, _finiteExtinction⟩
        exact
          ⟨n, package, by
            intro t x v w
            rw [← metricDerivative_eq]
            exact pointwiseEquation t x v w⟩) := by
  apply Subsingleton.elim

/--
The dependency direct pointwise equation payload is the direct stored
verification projection of the selected package-level scalar-pointwise payload.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_dependencies_to_surgery_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_direct_pointwise_equation_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, _pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_direct_pointwise_equation_payload
              package⟩) := by
  apply Subsingleton.elim

/--
The dependency-level pointwise equation payload is reconstructed from the
dependency-level direct stored-verification scalar equation payload.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_pointwise_equation_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package, by
            intro t x v w
            simpa
              [metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq]
              using directPayload t x v w⟩) := by
  apply Subsingleton.elim

/--
The older dependency-level equation/metric derivative payload is reconstructed
from the dependency-level direct stored-verification scalar equation payload.
-/
theorem equation_boundary_derivative_payload_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_derivative_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
              directPayload with
          ⟨_basePackage, _basePackage_eq, _equationBoundary, verification,
            verification_eq, metricDerivative, metricDerivative_eq,
            derivativeId, equationAtTime, _analyticBoundary,
            _finiteExtinction⟩
        exact
          ⟨n, package, verification, verification_eq, metricDerivative,
            metricDerivative_eq, derivativeId, equationAtTime⟩) := by
  apply Subsingleton.elim

/--
The dependency-level scalar-pointwise surgery payload is reconstructed from the
dependency-level direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
The dependency-level derivative payload is reconstructed from the
dependency-level direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_derivative_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
The dependency-level derivative payload is reconstructed from the selected
package-level scalar-pointwise payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_dependencies_to_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_derivative_payload_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
Dependency-level verification payload for the strengthened surgery family.

For each target manifold it selects a boundary-carrying surgery package and
records that its equation boundary, metric derivative, pointwise Ricci-flow
equation, and analytic-boundary statement all route through the projected
explicit Ricci-flow equation verification.
-/
abbrev EquationBoundaryVerificationPayload
    (_dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) : Prop :=
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ verification :
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _verification_eq :
          verification =
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
        ∃ equationBoundary :
          RicciFlowEquationBoundaryPackage
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)),
        ∃ _equationBoundary_eq :
          equationBoundary =
            equation_boundary_package_of_ricci_flow_equation_verification
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package package))
              verification,
        ∃ metricDerivative :
          MetricTimeDerivativeData
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _metricDerivative_eq :
          metricDerivative =
            metric_derivative_data_of_ricci_flow_equation_verification
              verification,
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package)))
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) ∧
          (∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                metricDerivative) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t) ∧
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))

/-- The dependency verification payload expands to its target-family statement. -/
theorem equationBoundaryVerificationPayload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    EquationBoundaryVerificationPayload dependencies =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ verification :
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _verification_eq :
          verification =
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
        ∃ equationBoundary :
          RicciFlowEquationBoundaryPackage
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)),
        ∃ _equationBoundary_eq :
          equationBoundary =
            equation_boundary_package_of_ricci_flow_equation_verification
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package package))
              verification,
        ∃ metricDerivative :
          MetricTimeDerivativeData
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _metricDerivative_eq :
          metricDerivative =
            metric_derivative_data_of_ricci_flow_equation_verification
              verification,
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package)))
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) ∧
          (∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                metricDerivative) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t) ∧
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))) :=
  rfl

/--
Strengthened dependencies expose a verification-routed payload for each
selected boundary-carrying surgery package.
-/
theorem equation_boundary_verification_payload_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    EquationBoundaryVerificationPayload dependencies := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  let verification :=
    ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
      package
  let equationBoundary :=
    equation_boundary_of_surgery_package_with_equation_boundary package
  let metricDerivative :=
    metric_derivative_data_of_ricci_flow_equation_verification verification
  exact
    ⟨n, package, verification, rfl, equationBoundary,
      equation_boundary_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
        package,
      metricDerivative, rfl,
      metric_time_derivative_identification_of_ricci_flow_equation_verification
        verification,
      equation_at_time_of_ricci_flow_equation_verification_projection
        verification,
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package⟩

/--
The dependency-level verification payload is selected from the stored
boundary-carrying surgery package family. Its equation and derivative fields
route through the projected explicit verification, while its analytic-boundary
field uses the boundary-backed surgery-package route.
-/
theorem equation_boundary_verification_payload_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_verification_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        let verification :=
          ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
            package
        let equationBoundary :=
          equation_boundary_of_surgery_package_with_equation_boundary package
        let metricDerivative :=
          metric_derivative_data_of_ricci_flow_equation_verification
            verification
        exact
          ⟨n, package, verification, rfl, equationBoundary,
            equation_boundary_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
              package,
            metricDerivative, rfl,
            metric_time_derivative_identification_of_ricci_flow_equation_verification
              verification,
            equation_at_time_of_ricci_flow_equation_verification_projection
              verification,
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

section VerificationFamilyBoundaryPackageProjections

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose
boundary-carrying surgery packages after applying the strengthened dependency
lift.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_and_verification_family :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty
          (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :=
  surgery_packages_with_equation_boundary_of_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family boundary package projection delegates to the
strengthened dependency projection after applying the verification-family lift.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_and_verification_family_eq :
    surgery_packages_with_equation_boundary_of_dependencies_and_verification_family
        dependencies verificationFamily =
      surgery_packages_with_equation_boundary_of_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
The projection-module boundary surgery family for a verification-family lift is
the structural surgery projection of the lifted dependency package.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_and_verification_family_to_structural_projection_eq :
    surgery_packages_with_equation_boundary_of_dependencies_and_verification_family
        dependencies verificationFamily =
      surgery_of_poincareProofDependenciesWithEquationBoundary
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
The projection-module boundary surgery family for a verification-family lift is
the ordinary surgery family mapped through the equation-verification
constructor.
-/
theorem surgery_packages_with_equation_boundary_of_dependencies_and_verification_family_to_lifted_surgery_eq :
    surgery_packages_with_equation_boundary_of_dependencies_and_verification_family
        dependencies verificationFamily =
      fun M => (surgery_of_poincareProofDependencies dependencies M).map
        (fun payload =>
          ⟨payload.1,
            surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
              payload.2
              (verificationFamily M payload)⟩) := by
  apply Subsingleton.elim

/--
Forgetting boundary data from the verification-family lift recovers the
ordinary surgery package family.
-/
theorem surgery_packages_of_dependencies_and_verification_family :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M) :=
  surgery_packages_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family ordinary surgery-package projection delegates through
the strengthened dependency lift.
-/
theorem surgery_packages_of_dependencies_and_verification_family_eq :
    surgery_packages_of_dependencies_and_verification_family
        dependencies verificationFamily =
      surgery_packages_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the stored ordinary surgery
package family.
-/
theorem surgery_packages_of_dependencies_and_verification_family_to_dependencies_eq :
    surgery_packages_of_dependencies_and_verification_family
        dependencies verificationFamily =
      surgery_packages_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The projection-module ordinary surgery family for a verification-family lift is
the structural ordinary surgery projection of the original dependencies.
-/
theorem surgery_packages_of_dependencies_and_verification_family_to_structural_projection_eq :
    surgery_packages_of_dependencies_and_verification_family
        dependencies verificationFamily =
      surgery_of_poincareProofDependencies dependencies := by
  apply Subsingleton.elim

/--
The verification-family lift exposes Ricci-flow equation-boundary packages for
the projected boundary-carrying surgery packages.
-/
theorem ricci_flow_equation_boundary_packages_of_dependencies_and_verification_family :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          Nonempty
            (RicciFlowEquationBoundaryPackage
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))) :=
  ricci_flow_equation_boundary_packages_of_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family equation-boundary package projection delegates through
the strengthened dependency lift.
-/
theorem ricci_flow_equation_boundary_packages_of_dependencies_and_verification_family_eq :
    ricci_flow_equation_boundary_packages_of_dependencies_and_verification_family
        dependencies verificationFamily =
      ricci_flow_equation_boundary_packages_of_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Ordinary dependencies plus explicit equation verifications expose the canonical
dependent verification payload for the strengthened lift.
-/
theorem equation_boundary_verification_payload_of_dependencies_and_verification_family :
    EquationBoundaryVerificationPayload
      (equation_boundary_dependencies_of_dependencies_and_verification_family
        dependencies verificationFamily) :=
  equation_boundary_verification_payload_of_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family dependent verification payload is the named payload of
the strengthened dependency lift.
-/
theorem equation_boundary_verification_payload_of_dependencies_and_verification_family_eq :
    equation_boundary_verification_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      equation_boundary_verification_payload_of_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

end VerificationFamilyBoundaryPackageProjections

/--
An arbitrary verification payload exposes the selected equation-boundary
package family without requiring callers to unpack the full payload shape.
-/
theorem ricci_flow_equation_boundary_packages_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          Nonempty
            (RicciFlowEquationBoundaryPackage
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))) := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, _verification, _verification_eq, equationBoundary,
      _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
      _derivativeId, _equationAtTime, _analyticBoundary⟩
  exact ⟨n, package, ⟨equationBoundary⟩⟩

/--
The equation-boundary package projection from a verification payload is the
boundary component stored in that payload.
-/
theorem ricci_flow_equation_boundary_packages_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ricci_flow_equation_boundary_packages_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, _verification, _verification_eq, equationBoundary,
            _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _equationAtTime, _analyticBoundary⟩
        exact ⟨n, package, ⟨equationBoundary⟩⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload forgets to the older equation/metric
derivative dependency payload.
-/
theorem equation_boundary_derivative_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ verification :
          RicciFlowEquationVerification
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _verification_eq :
          verification =
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
        ∃ metricDerivative :
          MetricTimeDerivativeData
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))),
        ∃ _metricDerivative_eq :
          metricDerivative =
            metric_derivative_data_of_surgery_package_with_equation_boundary
              package,
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package)))
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) ∧
          ∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                metricDerivative) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, verification, verification_eq, _equationBoundary,
      _equationBoundary_eq, metricDerivative, metricDerivative_eq_verification,
      derivativeId, equationAtTime, _analyticBoundary⟩
  have metricDerivative_eq_package :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package := by
    rw [metricDerivative_eq_verification, verification_eq]
    exact Eq.symm
      (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
        package)
  exact
    ⟨n, package, verification, verification_eq, metricDerivative,
      metricDerivative_eq_package, derivativeId, equationAtTime⟩

/--
The derivative projection from a verification payload is obtained by forgetting
its boundary package and analytic-boundary components.
-/
theorem equation_boundary_derivative_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, verification, verification_eq, _equationBoundary,
            _equationBoundary_eq, metricDerivative,
            metricDerivative_eq_verification, derivativeId, equationAtTime,
            _analyticBoundary⟩
        have metricDerivative_eq_package :
            metricDerivative =
              metric_derivative_data_of_surgery_package_with_equation_boundary
                package := by
          rw [metricDerivative_eq_verification, verification_eq]
          exact Eq.symm
            (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
              package)
        exact
          ⟨n, package, verification, verification_eq, metricDerivative,
            metricDerivative_eq_package, derivativeId, equationAtTime⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload exposes the pointwise Ricci-flow equation
through the selected boundary-carrying surgery package.
-/
theorem equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          ∀ (t : ℝ) (x : M)
            (v w : TangentSpace ThreeManifoldModelWithCorners x),
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_surgery_package_with_equation_boundary
                  package)) t x v w =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data
                  (ricci_flow_data_of_surgery_package
                    (surgery_package_of_equation_boundary_surgery_package
                      package))) t x v w := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, verification, verification_eq, _equationBoundary,
      _equationBoundary_eq, metricDerivative, metricDerivative_eq_verification,
      _derivativeId, equationAtTime, _analyticBoundary⟩
  have metricDerivative_eq_package :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package := by
    rw [metricDerivative_eq_verification, verification_eq]
    exact Eq.symm
      (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
        package)
  exact
    ⟨n, package, by
      intro t x v w
      rw [← metricDerivative_eq_package]
      exact congrArg (fun tensor => tensor x v w) (equationAtTime t)⟩

/--
The pointwise equation projection from a verification payload is obtained by
applying the stored tensor equation at `t x v w`.
-/
theorem equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, verification, verification_eq, _equationBoundary,
            _equationBoundary_eq, metricDerivative,
            metricDerivative_eq_verification, _derivativeId, equationAtTime,
            _analyticBoundary⟩
        have metricDerivative_eq_package :
            metricDerivative =
              metric_derivative_data_of_surgery_package_with_equation_boundary
                package := by
          rw [metricDerivative_eq_verification, verification_eq]
          exact Eq.symm
            (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
              package)
        exact
          ⟨n, package, by
            intro t x v w
            rw [← metricDerivative_eq_package]
            exact congrArg (fun tensor => tensor x v w)
              (equationAtTime t)⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload exposes the direct stored-verification
pointwise equation through the selected boundary-carrying surgery package.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload
            package := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, verification, verification_eq, _equationBoundary,
      _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
      _derivativeId, _equationAtTime, _analyticBoundary⟩
  exact
    ⟨n, package, by
      intro t x v w
      rw [← verification_eq]
      exact
        pointwise_equation_payload_of_ricci_flow_equation_verification
          verification t x v w⟩

/--
The direct pointwise equation projection from a verification payload is obtained
by applying its stored explicit verification at `t x v w`.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, verification, verification_eq, _equationBoundary,
            _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _equationAtTime, _analyticBoundary⟩
        exact
          ⟨n, package, by
            intro t x v w
            rw [← verification_eq]
            exact
              pointwise_equation_payload_of_ricci_flow_equation_verification
                verification t x v w⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload reconstructs the package-level
scalar-pointwise surgery payload for each selected package.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, verification, verification_eq, equationBoundary,
      _equationBoundary_eq, metricDerivative, metricDerivative_eq_verification,
      derivativeId, equationAtTime, analyticBoundary⟩
  have metricDerivative_eq_package :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package := by
    rw [metricDerivative_eq_verification, verification_eq]
    exact Eq.symm
      (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
        package)
  exact
    ⟨n, package,
      surgery_package_of_equation_boundary_surgery_package package,
      rfl, equationBoundary, verification, verification_eq,
      metricDerivative, metricDerivative_eq_package, derivativeId,
      (fun t x v w =>
        congrArg (fun tensor => tensor x v w) (equationAtTime t)),
      analyticBoundary,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The package-level scalar-pointwise surgery payload from a verification payload
is exactly the stored verification tuple plus finite-extinction projection.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, verification, verification_eq, equationBoundary,
            _equationBoundary_eq, metricDerivative,
            metricDerivative_eq_verification, derivativeId, equationAtTime,
            analyticBoundary⟩
        have metricDerivative_eq_package :
            metricDerivative =
              metric_derivative_data_of_surgery_package_with_equation_boundary
                package := by
          rw [metricDerivative_eq_verification, verification_eq]
          exact Eq.symm
            (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
              package)
        exact
          ⟨n, package,
            surgery_package_of_equation_boundary_surgery_package package,
            rfl, equationBoundary, verification, verification_eq,
            metricDerivative, metricDerivative_eq_package, derivativeId,
            (fun t x v w =>
              congrArg (fun tensor => tensor x v w) (equationAtTime t)),
            analyticBoundary,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The verification-payload direct pointwise equation payload is the direct
stored-verification projection of the reconstructed scalar-pointwise surgery
payload.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload_to_surgery_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, _pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_direct_pointwise_equation_payload
              package⟩) := by
  apply Subsingleton.elim

/--
The verification-payload pointwise equation projection is reconstructed from
the verification-payload direct stored-verification scalar equation payload.
-/
theorem equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package, by
            intro t x v w
            simpa
              [metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq]
              using directPayload t x v w⟩) := by
  apply Subsingleton.elim

/--
The older verification-payload equation/metric derivative projection is
reconstructed from the verification-payload direct stored-verification scalar
equation payload.
-/
theorem equation_boundary_derivative_payload_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
              directPayload with
          ⟨_basePackage, _basePackage_eq, _equationBoundary, verification,
            verification_eq, metricDerivative, metricDerivative_eq,
            derivativeId, equationAtTime, _analyticBoundary,
            _finiteExtinction⟩
        exact
          ⟨n, package, verification, verification_eq, metricDerivative,
            metricDerivative_eq, derivativeId, equationAtTime⟩) := by
  apply Subsingleton.elim

/--
The verification-payload scalar-pointwise surgery payload is reconstructed from
the verification-payload direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload exposes finite extinction through the
scalar-pointwise surgery payload reconstructed for each selected package.
-/
theorem finite_extinction_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _ _
  rcases
      surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        payload M with
    ⟨_n, _package, pointwisePayload⟩
  exact finite_extinction_of_pointwise_equation_payload pointwisePayload

/--
The finite-extinction projection from a verification payload is exactly the
finite-extinction projection of the selected boundary-carrying surgery package.
-/
theorem finite_extinction_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    finite_extinction_of_equation_boundary_verification_payload payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨_n, package, _verification, _verification_eq, _equationBoundary,
            _equationBoundary_eq, _metricDerivative,
            _metricDerivative_eq_verification, _derivativeId,
            _equationAtTime, _analyticBoundary⟩
        exact finite_extinction_of_surgery_package_with_equation_boundary
          package) := by
  apply Subsingleton.elim

/--
The verification-payload finite-extinction projection is the
finite-extinction projection of the reconstructed scalar-pointwise surgery
payload.
-/
theorem finite_extinction_of_equation_boundary_verification_payload_to_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    finite_extinction_of_equation_boundary_verification_payload payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨_n, _package, pointwisePayload⟩
        exact finite_extinction_of_pointwise_equation_payload
          pointwisePayload) := by
  apply Subsingleton.elim

/--
The verification-payload finite-extinction projection is reconstructed from the
verification-payload direct stored-verification scalar equation payload.
-/
theorem finite_extinction_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    finite_extinction_of_equation_boundary_verification_payload payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨_n, _package, directPayload⟩
        exact finite_extinction_of_direct_pointwise_equation_payload
          directPayload) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload reconstructs the full
derivative-strengthened surgery payload for each selected package.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
          SurgeryPackageWithEquationBoundaryDerivativePayload package := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, verification, verification_eq, equationBoundary,
      _equationBoundary_eq, metricDerivative, metricDerivative_eq_verification,
      derivativeId, equationAtTime, analyticBoundary⟩
  have metricDerivative_eq_package :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package := by
    rw [metricDerivative_eq_verification, verification_eq]
    exact Eq.symm
      (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
        package)
  exact
    ⟨n, package,
      surgery_package_of_equation_boundary_surgery_package package,
      rfl, equationBoundary, verification, verification_eq,
      metricDerivative, metricDerivative_eq_package, derivativeId,
      equationAtTime, analyticBoundary,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The full surgery-payload projection from a verification payload is exactly the
payload tuple plus the finite-extinction projection of the selected package.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, verification, verification_eq, equationBoundary,
            _equationBoundary_eq, metricDerivative,
            metricDerivative_eq_verification, derivativeId, equationAtTime,
            analyticBoundary⟩
        have metricDerivative_eq_package :
            metricDerivative =
              metric_derivative_data_of_surgery_package_with_equation_boundary
                package := by
          rw [metricDerivative_eq_verification, verification_eq]
          exact Eq.symm
            (metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
              package)
        exact
          ⟨n, package,
            surgery_package_of_equation_boundary_surgery_package package,
            rfl, equationBoundary, verification, verification_eq,
            metricDerivative, metricDerivative_eq_package, derivativeId,
            equationAtTime, analyticBoundary,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The verification-payload derivative surgery payload is reconstructed from the
verification-payload scalar-pointwise surgery payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload_to_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
The verification-payload derivative payload is reconstructed from the
verification-payload direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload reconstructs the boundary-carrying surgery
package payload for each selected package.
-/
theorem surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ _package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M,
        ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
        ∃ _equationBoundary :
          RicciFlowEquationBoundaryPackage
            (ricci_flow_data_of_surgery_package basePackage),
        ∃ _analyticBoundary :
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package basePackage),
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, _verification, _verification_eq, equationBoundary,
      _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
      _derivativeId, _equationAtTime, analyticBoundary⟩
  exact
    ⟨n, package,
      surgery_package_of_equation_boundary_surgery_package package,
      equationBoundary, analyticBoundary,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The boundary package projection from a verification payload is exactly the
payload tuple plus the finite-extinction projection of the selected package.
-/
theorem surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, _verification, _verification_eq, equationBoundary,
            _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _equationAtTime, analyticBoundary⟩
        exact
          ⟨n, package,
            surgery_package_of_equation_boundary_surgery_package package,
            equationBoundary, analyticBoundary,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The verification-payload boundary surgery-package projection is the forgetful
projection of the verification-payload scalar-pointwise surgery payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload_to_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
The verification-payload boundary surgery-package projection is reconstructed
from the verification-payload direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n, package,
            surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
An arbitrary verification payload exposes theorem-shaped analytic foundation
statements carrying the explicit equation boundary.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          AnalyticFoundationWithEquationBoundaryStatement flow := by
  intro M _ _ _ _ _ _
  rcases payload M with
    ⟨n, package, _verification, _verification_eq, _equationBoundary,
      _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
      _derivativeId, _equationAtTime, analyticBoundary⟩
  exact
    ⟨n,
      ricci_flow_data_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package),
      analyticBoundary⟩

/--
The analytic-boundary statement projection from a verification payload is the
analytic component stored in that payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases payload M with
          ⟨n, package, _verification, _verification_eq, _equationBoundary,
            _equationBoundary_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _equationAtTime, analyticBoundary⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
The verification-payload analytic/equation-boundary statement projection is
the analytic projection of the verification-payload scalar-pointwise surgery
payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload_to_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
The verification-payload analytic/equation-boundary statement projection is
reconstructed from the verification-payload direct stored-verification scalar
equation payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload_to_direct_pointwise_equation_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
              payload M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
A verification payload's analytic-boundary statement family exposes the
concrete equation-boundary package, derivative identification, tensor equation,
and scalar-pointwise equation for each target manifold.
-/
theorem equation_boundary_payload_statements_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ boundary : RicciFlowEquationBoundaryPackage flow,
          RicciFlowEquationBoundaryStatement flow ∧
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data flow)
            (metric_time_derivative_field_of_metric_derivative_data
              (metric_derivative_data_of_equation_boundary_package boundary)) ∧
          (∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data flow) t) ∧
          ∀ (t : ℝ) (x : M)
            (v w : TangentSpace ThreeManifoldModelWithCorners x),
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) t x v w =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data flow) t x v w := by
  intro M _ _ _ _ _ _
  rcases
      analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        payload M with
    ⟨n, flow, analyticBoundary⟩
  exact
    ⟨n, flow,
      equation_boundary_payload_of_analytic_foundation_with_equation_boundary
        analyticBoundary⟩

/--
The verification-payload equation-boundary payload family is obtained by
applying the generic analytic-boundary payload projection to each projected
analytic-boundary statement.
-/
theorem equation_boundary_payload_statements_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    equation_boundary_payload_statements_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
              payload M with
          ⟨n, flow, analyticBoundary⟩
        exact
          ⟨n, flow,
            equation_boundary_payload_of_analytic_foundation_with_equation_boundary
              analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
A verification payload's analytic-boundary statement family exposes both the
analytic derivation stack and the concrete equation-boundary payload for each
target manifold.
-/
theorem analytic_derivation_and_boundary_payload_statements_of_equation_boundary_verification_payload
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          AnalyticFoundationDerivationStatement flow ∧
          ∃ boundary : RicciFlowEquationBoundaryPackage flow,
            RicciFlowEquationBoundaryStatement flow ∧
            IsMetricTimeDerivativeOf
              (metric_of_ricci_flow_data flow)
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) ∧
            (∀ t : ℝ,
              metric_time_derivative_at_time_of_metric_derivative_field
                (metric_time_derivative_field_of_metric_derivative_data
                  (metric_derivative_data_of_equation_boundary_package
                    boundary)) t =
                ricci_flow_rhs_tensor
                  (curvature_data_of_ricci_flow_data flow) t) ∧
            ∀ (t : ℝ) (x : M)
              (v w : TangentSpace ThreeManifoldModelWithCorners x),
              metric_time_derivative_at_time_of_metric_derivative_field
                (metric_time_derivative_field_of_metric_derivative_data
                  (metric_derivative_data_of_equation_boundary_package
                    boundary)) t x v w =
                ricci_flow_rhs_tensor
                  (curvature_data_of_ricci_flow_data flow) t x v w := by
  intro M _ _ _ _ _ _
  rcases
      analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        payload M with
    ⟨n, flow, analyticBoundary⟩
  exact
    ⟨n, flow,
      analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
        analyticBoundary⟩

/--
The verification-payload derivation-and-boundary family is obtained by applying
the generic analytic derivation/boundary projection to each analytic-boundary
statement.
-/
theorem analytic_derivation_and_boundary_payload_statements_of_equation_boundary_verification_payload_eq
    {dependencies : PoincareProofDependenciesWithEquationBoundary.{u}}
    (payload : EquationBoundaryVerificationPayload dependencies) :
    analytic_derivation_and_boundary_payload_statements_of_equation_boundary_verification_payload
        payload =
      (by
        intro M _ _ _ _ _ _
        rcases
            analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
              payload M with
          ⟨n, flow, analyticBoundary⟩
        exact
          ⟨n, flow,
            analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
              analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
The named dependency equation-boundary package family is the projection of the
named verification payload.
-/
theorem ricci_flow_equation_boundary_packages_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ricci_flow_equation_boundary_packages_of_dependencies dependencies =
      ricci_flow_equation_boundary_packages_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency derivative payload is the derivative projection of the
named verification payload.
-/
theorem equation_boundary_derivative_payload_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_derivative_payload_of_dependencies dependencies =
      equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency pointwise equation payload is the pointwise projection of
the named verification payload.
-/
theorem equation_boundary_pointwise_equation_payload_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_pointwise_equation_payload_of_dependencies dependencies =
      equation_boundary_pointwise_equation_payload_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency direct pointwise equation payload is the direct
stored-verification projection of the named verification payload.
-/
theorem equation_boundary_direct_pointwise_equation_payload_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_direct_pointwise_equation_payload_of_dependencies
        dependencies =
      equation_boundary_direct_pointwise_equation_payload_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency full surgery derivative payload is reconstructed from the
named verification payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_derivative_payload_of_dependencies
        dependencies =
      surgery_package_with_equation_boundary_derivative_payload_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency boundary package payload is reconstructed from the named
verification payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    surgery_package_with_equation_boundary_payload_of_dependencies
        dependencies =
      surgery_package_with_equation_boundary_payload_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose theorem-shaped analytic foundation statements
that include the explicit Ricci-flow equation boundary.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          AnalyticFoundationWithEquationBoundaryStatement flow := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_with_equation_boundary_of_dependencies
      dependencies M with
    ⟨⟨n, package⟩⟩
  let basePackage := surgery_package_of_equation_boundary_surgery_package
    package
  exact
    ⟨n, ricci_flow_data_of_surgery_package basePackage,
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package⟩

/--
The strengthened dependency analytic-boundary statement projection is selected
from the stored boundary-carrying surgery package family.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_with_equation_boundary_of_dependencies
            dependencies M with
          ⟨⟨n, package⟩⟩
        let basePackage :=
          surgery_package_of_equation_boundary_surgery_package package
        exact
          ⟨n, ricci_flow_data_of_surgery_package basePackage,
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The named dependency analytic-boundary statement family is the analytic
projection of the named verification payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies =
      analytic_foundation_with_equation_boundary_statements_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
The named dependency analytic-boundary statement family is the analytic
projection of the full derivative-strengthened surgery payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies_to_surgery_derivative_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_derivative_payload_of_dependencies
              dependencies M with
          ⟨n, package, _basePackage, _basePackage_eq, _equationBoundary,
            _verification, _verification_eq, _metricDerivative,
            _metricDerivative_eq, _derivativeId, _equationAtTime,
            analyticBoundary, _finiteExtinction⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
The named dependency analytic-boundary statement family is the analytic
projection of the scalar-pointwise surgery payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies_to_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, pointwisePayload⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
              pointwisePayload⟩) := by
  apply Subsingleton.elim

/--
The named dependency analytic-boundary statement family is reconstructed from
the dependency-level direct stored-verification scalar equation payload.
-/
theorem analytic_foundation_with_equation_boundary_statements_of_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨n, package, directPayload⟩
        exact
          ⟨n,
            ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package),
            analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload
              directPayload⟩) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the concrete equation-boundary payload behind
their analytic-boundary statement family for every target manifold.
-/
theorem equation_boundary_payload_statements_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ boundary : RicciFlowEquationBoundaryPackage flow,
          RicciFlowEquationBoundaryStatement flow ∧
          IsMetricTimeDerivativeOf
            (metric_of_ricci_flow_data flow)
            (metric_time_derivative_field_of_metric_derivative_data
              (metric_derivative_data_of_equation_boundary_package boundary)) ∧
          (∀ t : ℝ,
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) t =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data flow) t) ∧
          ∀ (t : ℝ) (x : M)
            (v w : TangentSpace ThreeManifoldModelWithCorners x),
            metric_time_derivative_at_time_of_metric_derivative_field
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) t x v w =
              ricci_flow_rhs_tensor
                (curvature_data_of_ricci_flow_data flow) t x v w := by
  intro M _ _ _ _ _ _
  rcases
      analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies M with
    ⟨n, flow, analyticBoundary⟩
  exact
    ⟨n, flow,
      equation_boundary_payload_of_analytic_foundation_with_equation_boundary
        analyticBoundary⟩

/--
The named dependency equation-boundary payload family is the generic
analytic-boundary payload projection applied to each named analytic-boundary
statement.
-/
theorem equation_boundary_payload_statements_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_payload_statements_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            analytic_foundation_with_equation_boundary_statements_of_dependencies
              dependencies M with
          ⟨n, flow, analyticBoundary⟩
        exact
          ⟨n, flow,
            equation_boundary_payload_of_analytic_foundation_with_equation_boundary
              analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
The named dependency equation-boundary payload family is reconstructed from the
named verification payload.
-/
theorem equation_boundary_payload_statements_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    equation_boundary_payload_statements_of_dependencies dependencies =
      equation_boundary_payload_statements_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
Strengthened dependencies expose the analytic derivation stack together with
the concrete equation-boundary payload behind their analytic-boundary statement
family for every target manifold.
-/
theorem analytic_derivation_and_boundary_payload_statements_of_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          AnalyticFoundationDerivationStatement flow ∧
          ∃ boundary : RicciFlowEquationBoundaryPackage flow,
            RicciFlowEquationBoundaryStatement flow ∧
            IsMetricTimeDerivativeOf
              (metric_of_ricci_flow_data flow)
              (metric_time_derivative_field_of_metric_derivative_data
                (metric_derivative_data_of_equation_boundary_package
                  boundary)) ∧
            (∀ t : ℝ,
              metric_time_derivative_at_time_of_metric_derivative_field
                (metric_time_derivative_field_of_metric_derivative_data
                  (metric_derivative_data_of_equation_boundary_package
                    boundary)) t =
                ricci_flow_rhs_tensor
                  (curvature_data_of_ricci_flow_data flow) t) ∧
            ∀ (t : ℝ) (x : M)
              (v w : TangentSpace ThreeManifoldModelWithCorners x),
              metric_time_derivative_at_time_of_metric_derivative_field
                (metric_time_derivative_field_of_metric_derivative_data
                  (metric_derivative_data_of_equation_boundary_package
                    boundary)) t x v w =
                ricci_flow_rhs_tensor
                  (curvature_data_of_ricci_flow_data flow) t x v w := by
  intro M _ _ _ _ _ _
  rcases
      analytic_foundation_with_equation_boundary_statements_of_dependencies
        dependencies M with
    ⟨n, flow, analyticBoundary⟩
  exact
    ⟨n, flow,
      analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
        analyticBoundary⟩

/--
The named dependency derivation-and-boundary family is the generic
analytic-foundation derivation/boundary projection applied to each named
analytic-boundary statement.
-/
theorem analytic_derivation_and_boundary_payload_statements_of_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_derivation_and_boundary_payload_statements_of_dependencies
        dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            analytic_foundation_with_equation_boundary_statements_of_dependencies
              dependencies M with
          ⟨n, flow, analyticBoundary⟩
        exact
          ⟨n, flow,
            analytic_foundation_derivation_and_boundary_payload_of_with_equation_boundary
              analyticBoundary⟩) := by
  apply Subsingleton.elim

/--
The named dependency derivation-and-boundary family is reconstructed from the
named verification payload.
-/
theorem analytic_derivation_and_boundary_payload_statements_of_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    analytic_derivation_and_boundary_payload_statements_of_dependencies
        dependencies =
      analytic_derivation_and_boundary_payload_statements_of_equation_boundary_verification_payload
        (equation_boundary_verification_payload_of_dependencies
          dependencies) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes, for every target manifold, the
underlying finite-extinction surgery package and the three lower-level packages
projected from it: analytic foundation, Ricci-flow-with-surgery construction,
and Perelman singularity control.
-/
theorem surgery_package_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package : FiniteExtinctionSurgeryPackage n M,
        ∃ analyticPackage :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ _analyticPackage_eq :
          analyticPackage = analytic_foundation_of_surgery_package package,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq : flow = ricci_flow_data_of_surgery_package package,
        ∃ constructionPackage :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow,
        ∃ _constructionPackage_heq :
          HEq constructionPackage
            (surgery_construction_package_of_surgery_package package),
        ∃ controlPackage :
          PerelmanSingularityControlPackage (n := n) (M := M) flow,
          HEq controlPackage
            (perelman_control_package_of_surgery_package package) := by
  intro M _ _ _ _ _ _
  rcases surgery_packages_of_dependencies dependencies M with
    ⟨⟨n, package⟩⟩
  let analyticPackage := analytic_foundation_of_surgery_package package
  let flow := ricci_flow_data_of_surgery_package package
  let constructionPackage :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
    surgery_construction_package_of_surgery_package package
  let controlPackage :
      PerelmanSingularityControlPackage (n := n) (M := M) flow :=
    perelman_control_package_of_surgery_package package
  exact ⟨n, package, analyticPackage, rfl, flow, rfl, constructionPackage,
    HEq.rfl, controlPackage, HEq.rfl⟩

/--
The shared dependency surgery-package payload is selected from the stored
finite-extinction surgery package family and its package projections.
-/
theorem surgery_package_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_package_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_packages_of_dependencies dependencies M with
          ⟨⟨n, package⟩⟩
        let analyticPackage := analytic_foundation_of_surgery_package package
        let flow := ricci_flow_data_of_surgery_package package
        let constructionPackage :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
          surgery_construction_package_of_surgery_package package
        let controlPackage :
            PerelmanSingularityControlPackage (n := n) (M := M) flow :=
          perelman_control_package_of_surgery_package package
        exact ⟨n, package, analyticPackage, rfl, flow, rfl,
          constructionPackage, HEq.rfl, controlPackage, HEq.rfl⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies analytic-foundation packages for every
target manifold after smoothability regularity has been installed.
-/
theorem analytic_foundation_packages_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω,
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M) := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, _package, analyticPackage, _analyticPackage_eq, _flow, _flow_eq,
      _constructionPackage, _constructionPackage_eq, _controlPackage,
      _controlPackage_eq⟩
  exact ⟨⟨n, analyticPackage⟩⟩

/--
The dependency-level analytic-foundation package projection is obtained by
mapping the stored finite-extinction surgery package family to its analytic
foundation subpackage.
-/
theorem analytic_foundation_packages_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    analytic_foundation_packages_of_dependencies dependencies =
      fun M => (surgery_packages_of_dependencies dependencies M).map
        (fun payload =>
          ⟨payload.1, analytic_foundation_of_surgery_package payload.2⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the analytic-foundation payload through
the same finite-extinction surgery package selected from the dependency family,
with equality contracts for the analytic package and projected flow.
-/
theorem analytic_foundation_statement_payload_with_surgery_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
        ∃ package :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ _package_eq :
          package = analytic_foundation_of_surgery_package surgeryPackage,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_surgery_package surgeryPackage,
        ∃ _statement :
          RicciFlowAnalyticFoundationStatement
            ThreeManifoldModelWithCorners n M,
        ∃ _derivationStatement :
          AnalyticFoundationDerivationStatement flow,
        ∃ _subobligations :
          AnalyticFoundationSubobligationsPayload flow,
          SatisfiesRicciFlowEquation
            (metric_of_ricci_flow_data flow)
            (curvature_data_of_ricci_flow_data flow) := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
      _flow_eq, _constructionPackage, _constructionPackage_heq,
      _controlPackage, _controlPackage_heq⟩
  let package := analytic_foundation_of_surgery_package surgeryPackage
  let flow := ricci_flow_data_of_surgery_package surgeryPackage
  rcases analytic_foundation_payload_of_surgery_package surgeryPackage with
    ⟨statement, derivationStatement, subobligations, equationEvidence⟩
  exact ⟨n, surgeryPackage, package, rfl, flow, rfl, statement,
    derivationStatement, subobligations, equationEvidence⟩

/--
The dependency-level surgery-package analytic payload is selected from the
shared surgery-package payload and the surgery-package analytic payload.
-/
theorem analytic_foundation_statement_payload_with_surgery_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    analytic_foundation_statement_payload_with_surgery_package_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
            _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        let package := analytic_foundation_of_surgery_package surgeryPackage
        let flow := ricci_flow_data_of_surgery_package surgeryPackage
        rcases analytic_foundation_payload_of_surgery_package
            surgeryPackage with
          ⟨statement, derivationStatement, subobligations, equationEvidence⟩
        exact ⟨n, surgeryPackage, package, rfl, flow, rfl, statement,
          derivationStatement, subobligations, equationEvidence⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the fixed analytic-foundation payload:
the projected analytic package, its theorem-shaped statement, the fixed-flow
derivation statement, the statement-mediated analytic sub-obligation stack, and
Ricci-flow equation evidence.
-/
theorem analytic_foundation_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ package :
          RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_analytic_foundation_package package,
        ∃ _statement :
          RicciFlowAnalyticFoundationStatement
            ThreeManifoldModelWithCorners n M,
        ∃ _derivationStatement :
          AnalyticFoundationDerivationStatement flow,
        ∃ _subobligations :
          AnalyticFoundationSubobligationsPayload flow,
          SatisfiesRicciFlowEquation
            (metric_of_ricci_flow_data flow)
            (curvature_data_of_ricci_flow_data flow) := by
  intro M _ _ _ _ _ _
  rcases
      analytic_foundation_statement_payload_with_surgery_package_of_dependencies
        dependencies M with
    ⟨n, surgeryPackage, package, package_eq, flow, flow_eq, statement,
      derivationStatement, subobligations, equationEvidence⟩
  subst package
  exact ⟨n, analytic_foundation_of_surgery_package surgeryPackage, flow,
    flow_eq, statement, derivationStatement, subobligations,
    equationEvidence⟩

/--
The dependency-level analytic payload is selected from the package-routed
analytic payload by dropping the surgery package witness.
-/
theorem analytic_foundation_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    analytic_foundation_statement_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            analytic_foundation_statement_payload_with_surgery_package_of_dependencies
              dependencies M with
          ⟨n, surgeryPackage, package, package_eq, flow, flow_eq, statement,
            derivationStatement, subobligations, equationEvidence⟩
        subst package
        exact ⟨n, analytic_foundation_of_surgery_package surgeryPackage, flow,
          flow_eq, statement, derivationStatement, subobligations,
          equationEvidence⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped analytic foundation
statements for every target manifold after smoothability regularity has been
installed.
-/
theorem analytic_foundation_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          RicciFlowAnalyticFoundationStatement
            ThreeManifoldModelWithCorners n M := by
  intro M _ _ _ _ _ _
  rcases analytic_foundation_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _package, _flow, _flow_eq, statement, _derivationStatement,
      _subobligations, _equationEvidence⟩
  exact ⟨n, statement⟩

/--
The dependency-level analytic statement projection is the statement field
selected by the named analytic-foundation payload.
-/
theorem analytic_foundation_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    analytic_foundation_statements_of_dependencies dependencies M =
      ⟨payload.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
A completed dependency package supplies fixed-flow analytic derivation
statements for its projected Ricci-flow data.
-/
theorem analytic_foundation_derivation_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            AnalyticFoundationDerivationStatement flow := by
  intro M _ _ _ _ _ _
  rcases analytic_foundation_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _package, flow, _flow_eq, _statement, derivationStatement,
      _subobligations, _equationEvidence⟩
  exact ⟨n, flow, derivationStatement⟩

/--
The dependency-level analytic derivation-statement projection is selected from
the named analytic-foundation payload.
-/
theorem analytic_foundation_derivation_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    analytic_foundation_derivation_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level analytic derivation projection agrees with rebuilding the
fixed-flow derivation statement from the projected analytic sub-obligation
payload.
-/
theorem analytic_foundation_derivation_statements_of_dependencies_to_subobligations_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    analytic_foundation_derivation_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose_spec.choose,
        analytic_foundation_derivation_statement_of_subobligations_payload
          payload.choose_spec.choose_spec.choose
          payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies Ricci-flow data for every target
manifold once the smoothability regularity has been installed.
-/
theorem ricci_flow_data_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        Nonempty (Σ n : ℕ∞ω,
          RicciFlowData ThreeManifoldModelWithCorners n M) := by
  intro M _ _ _ _ _ _
  rcases analytic_foundation_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _package, flow, _flow_eq, _statement, _derivationStatement,
      _subobligations, _equationEvidence⟩
  exact ⟨⟨n, flow⟩⟩

/--
The dependency-level Ricci-flow data projection is selected from the named
analytic-foundation payload.
-/
theorem ricci_flow_data_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    ricci_flow_data_of_dependencies dependencies M =
      ⟨⟨payload.choose, payload.choose_spec.choose_spec.choose⟩⟩ := by
  dsimp

/--
A completed dependency package supplies Ricci-flow equation evidence for the
projected Ricci-flow data.
-/
theorem ricci_flow_equation_evidence_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            SatisfiesRicciFlowEquation
              (metric_of_ricci_flow_data flow)
              (curvature_data_of_ricci_flow_data flow) := by
  intro M _ _ _ _ _ _
  rcases analytic_foundation_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _package, flow, _flow_eq, _statement, _derivationStatement,
      _subobligations, equationEvidence⟩
  exact ⟨n, flow, equationEvidence⟩

/--
The dependency-level Ricci-flow equation evidence projection is selected from
the named analytic-foundation payload.
-/
theorem ricci_flow_equation_evidence_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    ricci_flow_equation_evidence_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec⟩ := by
  dsimp

/--
A completed dependency package supplies the named analytic Ricci-flow
sub-obligations for every target manifold.
-/
theorem analytic_foundation_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            AnalyticFoundationSubobligationsPayload flow := by
  intro M _ _ _ _ _ _
  rcases analytic_foundation_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _package, flow, _flow_eq, _statement, _derivationStatement,
      subobligations, _equationEvidence⟩
  exact ⟨n, flow, subobligations⟩

/--
The dependency-level analytic sub-obligation projection is selected from the
named analytic-foundation payload.
-/
theorem analytic_foundation_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    analytic_foundation_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level analytic sub-obligation projection agrees with the direct
package-level analytic sub-obligation bridge for the projected analytic package.
-/
theorem analytic_foundation_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      analytic_foundation_statement_payload_of_dependencies dependencies M
    analytic_foundation_subobligations_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_analytic_foundation_package
          payload.choose_spec.choose,
        analytic_foundation_subobligations_of_analytic_foundation_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies Ricci-flow-with-surgery construction
packages for every target manifold.
-/
theorem surgery_construction_packages_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, _package, _analyticPackage, _analyticPackage_eq, flow, _flow_eq,
      constructionPackage, _constructionPackage_eq, _controlPackage,
      _controlPackage_eq⟩
  exact ⟨n, flow, constructionPackage⟩

/--
The dependency-level surgery-construction package projection is selected from
the shared surgery-package payload.
-/
theorem surgery_construction_packages_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_construction_packages_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, _package, _analyticPackage, _analyticPackage_eq, flow,
            _flow_eq, constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        exact ⟨n, flow, constructionPackage⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the surgery-construction payload through
the same finite-extinction surgery package selected from the dependency family,
with equality contracts for the projected flow and construction package route.
-/
theorem surgery_construction_statement_payload_with_surgery_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_surgery_package surgeryPackage,
        ∃ constructionPackage :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow,
        ∃ _constructionPackage_heq :
          HEq constructionPackage
            (surgery_construction_package_of_surgery_package surgeryPackage),
        ∃ _statement : RicciFlowWithSurgeryConstructionStatement flow,
        ∃ _subobligations :
          RicciFlowWithSurgeryConstructionSubobligationsPayload flow,
          HasRicciFlowWithSurgery n M := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
      _flow_eq, _constructionPackage, _constructionPackage_heq,
      _controlPackage, _controlPackage_heq⟩
  let flow := ricci_flow_data_of_surgery_package surgeryPackage
  let constructionPackage :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
    surgery_construction_package_of_surgery_package surgeryPackage
  rcases surgery_construction_payload_of_construction_package
      constructionPackage with
    ⟨statement, subobligations, withSurgery⟩
  exact ⟨n, surgeryPackage, flow, rfl, constructionPackage, HEq.rfl,
    statement, subobligations, withSurgery⟩

/--
The dependency-level surgery-package construction payload is selected from the
shared surgery-package payload and the construction-package payload.
-/
theorem surgery_construction_statement_payload_with_surgery_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_construction_statement_payload_with_surgery_package_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
            _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        let flow := ricci_flow_data_of_surgery_package surgeryPackage
        let constructionPackage :
            RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
          surgery_construction_package_of_surgery_package surgeryPackage
        rcases surgery_construction_payload_of_construction_package
            constructionPackage with
          ⟨statement, subobligations, withSurgery⟩
        exact ⟨n, surgeryPackage, flow, rfl, constructionPackage, HEq.rfl,
          statement, subobligations, withSurgery⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the fixed surgery-construction payload:
the projected construction package, its theorem-shaped construction statement,
the statement's sub-obligation stack, and the Ricci-flow-with-surgery witness
recovered from that statement.
-/
theorem surgery_construction_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _constructionPackage :
          RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow,
        ∃ _statement : RicciFlowWithSurgeryConstructionStatement flow,
        ∃ _subobligations :
          RicciFlowWithSurgeryConstructionSubobligationsPayload flow,
          HasRicciFlowWithSurgery n M := by
  intro M _ _ _ _ _ _
  rcases
      surgery_construction_statement_payload_with_surgery_package_of_dependencies
        dependencies M with
    ⟨n, _surgeryPackage, flow, _flow_eq, constructionPackage,
      _constructionPackage_heq, statement, subobligations, withSurgery⟩
  exact ⟨n, flow, constructionPackage, statement, subobligations, withSurgery⟩

/--
The dependency-level surgery-construction payload is selected from the
package-routed construction payload by dropping the surgery package witness.
-/
theorem surgery_construction_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    surgery_construction_statement_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            surgery_construction_statement_payload_with_surgery_package_of_dependencies
              dependencies M with
          ⟨n, _surgeryPackage, flow, _flow_eq, constructionPackage,
            _constructionPackage_heq, statement, subobligations,
            withSurgery⟩
        exact ⟨n, flow, constructionPackage, statement, subobligations,
          withSurgery⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped surgery-construction
statements for every target manifold.
-/
theorem surgery_construction_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            RicciFlowWithSurgeryConstructionStatement flow := by
  intro M _ _ _ _ _ _
  rcases surgery_construction_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _constructionPackage, statement, _subobligations,
      _withSurgery⟩
  exact ⟨n, flow, statement⟩

/--
The dependency-level surgery-construction statement projection is selected from
the named surgery-construction payload.
-/
theorem surgery_construction_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      surgery_construction_statement_payload_of_dependencies dependencies M
    surgery_construction_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
A completed dependency package supplies the named surgery-construction
sub-obligations for every target manifold.
-/
theorem surgery_construction_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            RicciFlowWithSurgeryConstructionSubobligationsPayload flow := by
  intro M _ _ _ _ _ _
  rcases surgery_construction_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _constructionPackage, _statement, subobligations,
      _withSurgery⟩
  exact ⟨n, flow, subobligations⟩

/--
The dependency-level surgery-construction sub-obligation projection is selected
from the named surgery-construction payload.
-/
theorem surgery_construction_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      surgery_construction_statement_payload_of_dependencies dependencies M
    surgery_construction_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level surgery-construction sub-obligation projection agrees
with the direct construction-package sub-obligation bridge for the projected
construction package.
-/
theorem surgery_construction_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      surgery_construction_statement_payload_of_dependencies dependencies M
    surgery_construction_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        surgery_construction_subobligations_of_construction_package
          payload.choose_spec.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the Perelman-control payload through the
same finite-extinction surgery package selected from the dependency family,
with equality contracts for the projected flow and Perelman-control route.
-/
theorem perelman_control_statement_payload_with_surgery_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_surgery_package surgeryPackage,
        ∃ controlPackage :
          PerelmanSingularityControlPackage (n := n) (M := M) flow,
        ∃ _controlPackage_heq :
          HEq controlPackage
            (perelman_control_package_of_surgery_package surgeryPackage),
        ∃ _statement : PerelmanSingularityControlStatement flow,
        ∃ _subobligations :
          PerelmanSingularityControlSubobligationsPayload flow,
        ∃ _monotonicityBlowupSubobligations :
          PerelmanMonotonicityBlowupSubobligationsPayload flow,
          HasPerelmanSingularityControl (n := n) (M := M) flow := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
      _flow_eq, _constructionPackage, _constructionPackage_heq,
      _controlPackage, _controlPackage_heq⟩
  let flow := ricci_flow_data_of_surgery_package surgeryPackage
  let controlPackage :
      PerelmanSingularityControlPackage (n := n) (M := M) flow :=
    perelman_control_package_of_surgery_package surgeryPackage
  rcases perelman_control_payload_of_package controlPackage with
    ⟨statement, subobligations, monotonicityBlowupSubobligations, control⟩
  exact ⟨n, surgeryPackage, flow, rfl, controlPackage, HEq.rfl,
    statement, subobligations, monotonicityBlowupSubobligations, control⟩

/--
The dependency-level surgery-package Perelman-control payload is selected from
the shared surgery-package payload and the Perelman package payload.
-/
theorem perelman_control_statement_payload_with_surgery_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    perelman_control_statement_payload_with_surgery_package_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
            _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        let flow := ricci_flow_data_of_surgery_package surgeryPackage
        let controlPackage :
            PerelmanSingularityControlPackage (n := n) (M := M) flow :=
          perelman_control_package_of_surgery_package surgeryPackage
        rcases perelman_control_payload_of_package controlPackage with
          ⟨statement, subobligations, monotonicityBlowupSubobligations,
            control⟩
        exact ⟨n, surgeryPackage, flow, rfl, controlPackage, HEq.rfl,
          statement, subobligations, monotonicityBlowupSubobligations,
          control⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped Perelman
singularity-control statements for its projected Ricci-flow data.
-/
theorem perelman_control_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ _controlPackage :
            PerelmanSingularityControlPackage (n := n) (M := M) flow,
          ∃ _statement : PerelmanSingularityControlStatement flow,
          ∃ _subobligations :
            PerelmanSingularityControlSubobligationsPayload flow,
          ∃ _monotonicityBlowupSubobligations :
            PerelmanMonotonicityBlowupSubobligationsPayload flow,
            HasPerelmanSingularityControl (n := n) (M := M) flow := by
  intro M _ _ _ _ _ _
  rcases
      perelman_control_statement_payload_with_surgery_package_of_dependencies
        dependencies M with
    ⟨n, _surgeryPackage, flow, _flow_eq, controlPackage,
      _controlPackage_heq, statement, subobligations,
      monotonicityBlowupSubobligations, control⟩
  exact ⟨n, flow, controlPackage, statement, subobligations,
    monotonicityBlowupSubobligations, control⟩

/--
The dependency-level Perelman-control payload is selected from the
package-routed Perelman payload by dropping the surgery package witness.
-/
theorem perelman_control_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    perelman_control_statement_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            perelman_control_statement_payload_with_surgery_package_of_dependencies
              dependencies M with
          ⟨n, _surgeryPackage, flow, _flow_eq, controlPackage,
            _controlPackage_heq, statement, subobligations,
            monotonicityBlowupSubobligations, control⟩
        exact ⟨n, flow, controlPackage, statement, subobligations,
          monotonicityBlowupSubobligations, control⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped Perelman
singularity-control statements for its projected Ricci-flow data.
-/
theorem perelman_control_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            PerelmanSingularityControlStatement flow := by
  intro M _ _ _ _ _ _
  rcases perelman_control_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _controlPackage, statement, _subobligations,
      _monotonicityBlowupSubobligations, _control⟩
  exact ⟨n, flow, statement⟩

/--
The dependency-level Perelman statement projection is selected from the named
Perelman-control payload.
-/
theorem perelman_control_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_control_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
A completed dependency package supplies Perelman singularity-control evidence
for its projected Ricci-flow data.
-/
theorem perelman_control_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            HasPerelmanSingularityControl (n := n) (M := M) flow := by
  intro M _ _ _ _ _ _
  rcases perelman_control_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _controlPackage, _statement, _subobligations,
      _monotonicityBlowupSubobligations, control⟩
  exact ⟨n, flow, control⟩

/--
The dependency-level Perelman-control evidence projection is selected from the
named Perelman-control payload.
-/
theorem perelman_control_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_control_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec⟩ := by
  dsimp

/--
A completed dependency package supplies Perelman control packages for every
target manifold after smoothability regularity has been installed.
-/
theorem perelman_control_packages_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            PerelmanSingularityControlPackage (n := n) (M := M) flow := by
  intro M _ _ _ _ _ _
  rcases perelman_control_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, controlPackage, _statement, _subobligations,
      _monotonicityBlowupSubobligations, _control⟩
  exact ⟨n, flow, controlPackage⟩

/--
The dependency-level Perelman package projection is selected from the named
Perelman-control payload.
-/
theorem perelman_control_packages_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_control_packages_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
A completed dependency package supplies the named Perelman sub-obligations for
every target manifold.
-/
theorem perelman_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            PerelmanSingularityControlSubobligationsPayload flow := by
  intro M _ _ _ _ _ _
  rcases perelman_control_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _controlPackage, _statement, subobligations,
      _monotonicityBlowupSubobligations, _control⟩
  exact ⟨n, flow, subobligations⟩

/--
The dependency-level Perelman sub-obligation projection is selected from the
named Perelman-control payload.
-/
theorem perelman_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level full Perelman sub-obligation projection agrees with the
direct Perelman-package sub-obligation bridge for the projected control package.
-/
theorem perelman_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        perelman_subobligations_of_package
          payload.choose_spec.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the Perelman monotonicity and blow-up
analysis inputs that feed no-local-collapsing and canonical neighborhoods.
-/
theorem perelman_monotonicity_blowup_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
            PerelmanMonotonicityBlowupSubobligationsPayload flow := by
  intro M _ _ _ _ _ _
  rcases perelman_control_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, _controlPackage, _statement, _subobligations,
      monotonicityBlowupSubobligations, _control⟩
  exact ⟨n, flow, monotonicityBlowupSubobligations⟩

/--
The dependency-level Perelman monotonicity/blow-up projection is selected from
the named Perelman-control payload.
-/
theorem perelman_monotonicity_blowup_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_monotonicity_blowup_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level Perelman monotonicity/blow-up projection agrees with the
direct Perelman-package monotonicity/blow-up bridge for the projected control
package.
-/
theorem perelman_monotonicity_blowup_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      perelman_control_statement_payload_of_dependencies dependencies M
    perelman_monotonicity_blowup_subobligations_of_dependencies
        dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        perelman_monotonicity_blowup_subobligations_of_package
          payload.choose_spec.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the finite-extinction width/full
sub-obligation statement payload through the same finite-extinction surgery
package selected from the dependency family, pinning the flow, surgery,
Perelman control, statements, and package statement to that route.
-/
theorem finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_surgery_package surgeryPackage,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ _surgery_eq :
          surgery = ricci_flow_with_surgery_of_surgery_package surgeryPackage,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _control_heq :
          HEq control
            (perelman_singularity_control_of_surgery_package surgeryPackage),
        ∃ widthStatement :
          FiniteExtinctionWidthSubobligationsStatement flow surgery control,
        ∃ _widthStatement_heq :
          HEq widthStatement
            (finite_extinction_width_subobligations_statement_of_surgery_package
              surgeryPackage),
        ∃ subobligationsStatement :
          FiniteExtinctionSubobligationsStatement flow surgery control,
        ∃ _subobligationsStatement_heq :
          HEq subobligationsStatement
            (finite_extinction_subobligations_statement_of_surgery_package
              surgeryPackage),
        ∃ _widthSubobligations :
          FiniteExtinctionWidthSubobligationsPayload flow surgery control,
        ∃ _subobligations :
          FiniteExtinctionSubobligationsPayload flow surgery control,
        ∃ packageStatement : FiniteExtinctionStatement n M,
          packageStatement =
            finite_extinction_statement_of_surgery_package
              surgeryPackage := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
      _flow_eq, _constructionPackage, _constructionPackage_heq,
      _controlPackage, _controlPackage_heq⟩
  let flow := ricci_flow_data_of_surgery_package surgeryPackage
  let surgery := ricci_flow_with_surgery_of_surgery_package surgeryPackage
  let control := perelman_singularity_control_of_surgery_package surgeryPackage
  let widthStatement :=
    finite_extinction_width_subobligations_statement_of_surgery_package
      surgeryPackage
  let subobligationsStatement :=
    finite_extinction_subobligations_statement_of_surgery_package surgeryPackage
  let widthSubobligations :=
    finite_extinction_width_subobligations_of_statement widthStatement
  let subobligations :=
    finite_extinction_subobligations_of_statement subobligationsStatement
  let packageStatement := finite_extinction_statement_of_surgery_package
    surgeryPackage
  exact ⟨n, surgeryPackage, flow, rfl, surgery, rfl, control, HEq.rfl,
    widthStatement, HEq.rfl, subobligationsStatement, HEq.rfl,
    widthSubobligations, subobligations, packageStatement, rfl⟩

/--
The dependency-level surgery-package finite-extinction sub-obligation payload is
selected from the named surgery package payload and the package-level
sub-obligation statement projections.
-/
theorem finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
            _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        let flow := ricci_flow_data_of_surgery_package surgeryPackage
        let surgery := ricci_flow_with_surgery_of_surgery_package
          surgeryPackage
        let control := perelman_singularity_control_of_surgery_package
          surgeryPackage
        let widthStatement :=
          finite_extinction_width_subobligations_statement_of_surgery_package
            surgeryPackage
        let subobligationsStatement :=
          finite_extinction_subobligations_statement_of_surgery_package
            surgeryPackage
        let widthSubobligations :=
          finite_extinction_width_subobligations_of_statement widthStatement
        let subobligations :=
          finite_extinction_subobligations_of_statement
            subobligationsStatement
        let packageStatement := finite_extinction_statement_of_surgery_package
          surgeryPackage
        exact ⟨n, surgeryPackage, flow, rfl, surgery, rfl, control, HEq.rfl,
          widthStatement, HEq.rfl, subobligationsStatement, HEq.rfl,
          widthSubobligations, subobligations, packageStatement, rfl⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped finite-extinction width
sub-obligation statements for every target manifold.
-/
theorem finite_extinction_subobligations_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _widthStatement :
            FiniteExtinctionWidthSubobligationsStatement flow surgery control,
          ∃ _subobligationsStatement :
            FiniteExtinctionSubobligationsStatement flow surgery control,
          ∃ _widthSubobligations :
            FiniteExtinctionWidthSubobligationsPayload flow surgery control,
          ∃ _subobligations :
            FiniteExtinctionSubobligationsPayload flow surgery control,
            FiniteExtinctionStatement n M := by
  intro M _ _ _ _ _ _
  rcases
      finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
        dependencies M with
    ⟨n, _surgeryPackage, flow, _flow_eq, surgery, _surgery_eq, control,
      _control_heq, widthStatement, _widthStatement_heq,
      subobligationsStatement, _subobligationsStatement_heq,
      widthSubobligations, subobligations, packageStatement,
      _packageStatement_eq⟩
  exact ⟨n, flow, surgery, control,
    widthStatement, subobligationsStatement, widthSubobligations,
    subobligations, packageStatement⟩

/--
The dependency-level finite-extinction sub-obligation payload is selected from
the named surgery-package payload by dropping the package and equality
witnesses.
-/
theorem finite_extinction_subobligations_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_subobligations_statement_payload_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
              dependencies M with
          ⟨n, _surgeryPackage, flow, _flow_eq, surgery, _surgery_eq,
            control, _control_heq, widthStatement, _widthStatement_heq,
            subobligationsStatement, _subobligationsStatement_heq,
            widthSubobligations, subobligations, packageStatement,
            _packageStatement_eq⟩
        exact ⟨n, flow, surgery, control,
          widthStatement, subobligationsStatement, widthSubobligations,
          subobligations, packageStatement⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped finite-extinction width
sub-obligation statements for every target manifold.
-/
theorem finite_extinction_width_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
            FiniteExtinctionWidthSubobligationsStatement
              flow surgery control := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_subobligations_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, surgery, control, widthStatement,
      _subobligationsStatement, _widthSubobligations, _subobligations,
      _packageStatement⟩
  exact ⟨n, flow, surgery, control, widthStatement⟩

/--
The dependency-level finite-extinction width-statement projection is selected
from the named finite-extinction sub-obligation statement payload.
-/
theorem finite_extinction_width_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_of_dependencies
        dependencies M
    finite_extinction_width_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction width-statement projection follows the
direct width statement of the selected surgery package.
-/
theorem finite_extinction_width_statements_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_width_statements_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_width_subobligations_statement_of_surgery_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped full finite-extinction
sub-obligation statements for every target manifold.
-/
theorem finite_extinction_subobligations_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
            FiniteExtinctionSubobligationsStatement flow surgery control := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_subobligations_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, surgery, control, _widthStatement,
      subobligationsStatement, _widthSubobligations, _subobligations,
      _packageStatement⟩
  exact ⟨n, flow, surgery, control, subobligationsStatement⟩

/--
The dependency-level finite-extinction full sub-obligation statement projection
is selected from the named finite-extinction sub-obligation statement payload.
-/
theorem finite_extinction_subobligations_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_of_dependencies
        dependencies M
    finite_extinction_subobligations_statements_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction full-statement projection follows the
direct full sub-obligation statement of the selected surgery package.
-/
theorem finite_extinction_subobligations_statements_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_subobligations_statements_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_subobligations_statement_of_surgery_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the final finite-extinction statement
payload through the same finite-extinction surgery package selected from the
dependency family, pinning both the package statement and the statement rebuilt
through the full sub-obligation route to named projections.
-/
theorem finite_extinction_statement_payload_with_surgery_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ surgeryPackage : FiniteExtinctionSurgeryPackage n M,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ _flow_eq :
          flow = ricci_flow_data_of_surgery_package surgeryPackage,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ _surgery_eq :
          surgery = ricci_flow_with_surgery_of_surgery_package surgeryPackage,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _control_heq :
          HEq control
            (perelman_singularity_control_of_surgery_package surgeryPackage),
        ∃ packageStatement : FiniteExtinctionStatement n M,
        ∃ _packageStatement_eq :
          packageStatement =
            finite_extinction_statement_of_surgery_package surgeryPackage,
        ∃ subobligationsStatement :
          FiniteExtinctionSubobligationsStatement flow surgery control,
        ∃ _subobligationsStatement_heq :
          HEq subobligationsStatement
            (finite_extinction_subobligations_statement_of_surgery_package
              surgeryPackage),
        ∃ viaSubobligationsStatement : FiniteExtinctionStatement n M,
        ∃ _viaSubobligationsStatement_eq :
          viaSubobligationsStatement =
            finite_extinction_statement_of_subobligations_statement
              subobligationsStatement,
        ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
        ∃ _derivation_eq :
          derivation =
            finite_extinction_derivation_of_subobligations_statement
              subobligationsStatement,
        ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
          finiteExtinction =
            finite_extinction_of_subobligations_statement
              subobligationsStatement := by
  intro M _ _ _ _ _ _
  rcases surgery_package_payload_of_dependencies dependencies M with
    ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
      _flow_eq, _constructionPackage, _constructionPackage_heq,
      _controlPackage, _controlPackage_heq⟩
  let flow := ricci_flow_data_of_surgery_package surgeryPackage
  let surgery := ricci_flow_with_surgery_of_surgery_package surgeryPackage
  let control := perelman_singularity_control_of_surgery_package surgeryPackage
  let packageStatement :=
    finite_extinction_statement_of_surgery_package surgeryPackage
  let subobligationsStatement :=
    finite_extinction_subobligations_statement_of_surgery_package surgeryPackage
  let viaSubobligationsStatement :=
    finite_extinction_statement_of_subobligations_statement
      subobligationsStatement
  let derivation :=
    finite_extinction_derivation_of_subobligations_statement
      subobligationsStatement
  let finiteExtinction :=
    finite_extinction_of_subobligations_statement subobligationsStatement
  exact ⟨n, surgeryPackage, flow, rfl, surgery, rfl, control, HEq.rfl,
    packageStatement, rfl, subobligationsStatement, HEq.rfl,
    viaSubobligationsStatement, rfl, derivation, rfl, finiteExtinction,
    rfl⟩

/--
The dependency-level surgery-package finite-extinction payload is selected from
the named surgery package payload and the package-level finite-extinction
projections.
-/
theorem finite_extinction_statement_payload_with_surgery_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_statement_payload_with_surgery_package_of_dependencies
      dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨n, surgeryPackage, _analyticPackage, _analyticPackage_eq, _flow,
            _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        let flow := ricci_flow_data_of_surgery_package surgeryPackage
        let surgery := ricci_flow_with_surgery_of_surgery_package surgeryPackage
        let control := perelman_singularity_control_of_surgery_package
          surgeryPackage
        let packageStatement :=
          finite_extinction_statement_of_surgery_package surgeryPackage
        let subobligationsStatement :=
          finite_extinction_subobligations_statement_of_surgery_package
            surgeryPackage
        let viaSubobligationsStatement :=
          finite_extinction_statement_of_subobligations_statement
            subobligationsStatement
        let derivation :=
          finite_extinction_derivation_of_subobligations_statement
            subobligationsStatement
        let finiteExtinction :=
          finite_extinction_of_subobligations_statement
            subobligationsStatement
        exact ⟨n, surgeryPackage, flow, rfl, surgery, rfl, control, HEq.rfl,
          packageStatement, rfl, subobligationsStatement, HEq.rfl,
          viaSubobligationsStatement, rfl, derivation, rfl, finiteExtinction,
          rfl⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package exposes the fixed finite-extinction payload:
the package-level theorem-shaped statement, the full sub-obligation statement,
the statement rebuilt through that sub-obligation route, the derivation
certificate, and the resulting finite-extinction witness.
-/
theorem finite_extinction_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
        ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        ∃ surgery : HasRicciFlowWithSurgery n M,
        ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        ∃ _packageStatement : FiniteExtinctionStatement n M,
        ∃ _subobligationsStatement :
          FiniteExtinctionSubobligationsStatement flow surgery control,
        ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
        ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
          FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _ _
  rcases
      finite_extinction_statement_payload_with_surgery_package_of_dependencies
        dependencies M with
    ⟨n, _surgeryPackage, flow, _flow_eq, surgery, _surgery_eq, control,
      _control_heq, packageStatement, _packageStatement_eq,
      subobligationsStatement, _subobligationsStatement_heq,
      viaSubobligationsStatement, _viaSubobligationsStatement_eq,
      derivation, _derivation_eq, finiteExtinction, _finiteExtinction_eq⟩
  exact ⟨n, flow, surgery, control, packageStatement,
    subobligationsStatement, viaSubobligationsStatement, derivation,
    finiteExtinction⟩

/--
The dependency-level finite-extinction payload is selected from the named
surgery-package payload by dropping the package and equality witnesses.
-/
theorem finite_extinction_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_statement_payload_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _ _
        rcases
            finite_extinction_statement_payload_with_surgery_package_of_dependencies
              dependencies M with
          ⟨n, _surgeryPackage, flow, _flow_eq, surgery, _surgery_eq,
            control, _control_heq, packageStatement, _packageStatement_eq,
            subobligationsStatement, _subobligationsStatement_heq,
            viaSubobligationsStatement, _viaSubobligationsStatement_eq,
            derivation, _derivation_eq, finiteExtinction,
            _finiteExtinction_eq⟩
        exact ⟨n, flow, surgery, control, packageStatement,
          subobligationsStatement, viaSubobligationsStatement, derivation,
          finiteExtinction⟩) := by
  apply Subsingleton.elim

/--
The dependency-level finite-extinction statement payload is the package-level
statement payload of the selected surgery package, with the package index kept
visible.
-/
theorem finite_extinction_statement_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_statement_payload_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_statement_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_subobligations_statement_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_statement_of_subobligations_statement
          (finite_extinction_subobligations_statement_of_surgery_package
            payload.choose_spec.choose),
        finite_extinction_derivation_of_subobligations_statement
          (finite_extinction_subobligations_statement_of_surgery_package
            payload.choose_spec.choose),
        finite_extinction_of_subobligations_statement
          (finite_extinction_subobligations_statement_of_surgery_package
            payload.choose_spec.choose)⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the full local surgery derivation stack
for finite extinction.
-/
theorem finite_extinction_derivation_stack_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
            HasFiniteExtinctionDerivation flow surgery control := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, surgery, control, _packageStatement, _statement,
      _viaSubobligationsStatement, derivation, _finiteExtinction⟩
  exact ⟨n, flow, surgery, control, derivation⟩

/--
The dependency-level finite-extinction derivation-stack projection is selected
from the named finite-extinction statement payload.
-/
theorem finite_extinction_derivation_stack_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_of_dependencies dependencies M
    finite_extinction_derivation_stack_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction derivation stack follows the
sub-obligation statement of the selected surgery package.
-/
theorem finite_extinction_derivation_stack_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_derivation_stack_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_derivation_of_subobligations_statement
          (finite_extinction_subobligations_statement_of_surgery_package
            payload.choose_spec.choose)⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the finite-extinction topological and
width-analysis inputs before the final extinction derivation is applied.
-/
theorem finite_extinction_width_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
          ∃ sweepout :
            HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
          ∃ _sweepoutParameterSpace :
            HasFiniteExtinctionSweepoutParameterSpace M
              _finiteFundamentalGroup,
          ∃ _sweepoutContinuity :
            HasFiniteExtinctionSweepoutContinuity M
              _finiteFundamentalGroup sweepout,
          ∃ _sweepoutAreaBound :
            HasFiniteExtinctionSweepoutAreaBound M
              _finiteFundamentalGroup sweepout,
          ∃ _sweepoutNontriviality :
            HasFiniteExtinctionSweepoutNontriviality M
              _finiteFundamentalGroup sweepout,
          ∃ _areaFunctional :
            HasFiniteExtinctionAreaFunctionalSetup
              flow surgery control _finiteFundamentalGroup sweepout,
          ∃ widthDefinition :
            HasFiniteExtinctionMinMaxWidthDefinition
              flow surgery control _finiteFundamentalGroup sweepout,
          ∃ _widthCompactness :
            HasFiniteExtinctionWidthCompactness
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _widthLowerSemicontinuity :
            HasFiniteExtinctionWidthLowerSemicontinuity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minimizingSequence :
            HasFiniteExtinctionMinimizingSequence
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _pullTightArgument :
            HasFiniteExtinctionPullTightArgument
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minMaxStationarity :
            HasFiniteExtinctionMinMaxStationarity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minSurfaceRegularity :
            HasFiniteExtinctionMinSurfaceRegularity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _positiveWidth :
            HasFiniteExtinctionPositiveWidth
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ widthTheory :
            HasFiniteExtinctionWidthTheory flow surgery control,
          ∃ _firstVariationFormula :
            HasFiniteExtinctionFirstVariationFormula
              flow surgery control widthTheory,
          ∃ _secondVariationInequality :
            HasFiniteExtinctionSecondVariationInequality
              flow surgery control widthTheory,
          ∃ _gaussBonnetEstimate :
            HasFiniteExtinctionGaussBonnetEstimate
              flow surgery control widthTheory,
          ∃ _scalarCurvatureWidthBound :
            HasFiniteExtinctionScalarCurvatureWidthBound
              flow surgery control widthTheory,
          ∃ widthEvolution :
            HasFiniteExtinctionWidthEvolution
              flow surgery control widthTheory,
          ∃ _widthDifferentialInequality :
            HasFiniteExtinctionWidthDifferentialInequality
              flow surgery control widthTheory,
          ∃ _surgeryMetricComparison :
            HasFiniteExtinctionSurgeryMetricComparison
              flow surgery control widthTheory widthEvolution,
          ∃ _surgeryWidthComparisonMap :
            HasFiniteExtinctionSurgeryWidthComparisonMap
              flow surgery control widthTheory widthEvolution,
          ∃ _surgeryWidthDrop :
            HasFiniteExtinctionSurgeryWidthDrop
              flow surgery control widthTheory widthEvolution,
          ∃ surgeryDiscardControl :
            HasFiniteExtinctionSurgeryDiscardControl
              flow surgery control widthTheory widthEvolution,
          ∃ _discardedComponentWidthNeutrality :
            HasFiniteExtinctionDiscardedComponentWidthNeutrality
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _discardedComponentSweepoutTriviality :
            HasFiniteExtinctionDiscardedComponentSweepoutTriviality
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _discardedComponentClassification :
            HasFiniteExtinctionDiscardedComponentClassification
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _survivingComponentTracking :
            HasFiniteExtinctionSurvivingComponentTracking
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
            HasFiniteExtinctionComponentTopology
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_subobligations_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, surgery, control, _widthStatement,
      _subobligationsStatement, widthSubobligations, _subobligations,
      _packageStatement⟩
  exact ⟨n, flow, surgery, control, widthSubobligations⟩

/--
The dependency-level finite-extinction width sub-obligation projection is
selected from the named finite-extinction sub-obligation statement payload.
-/
theorem finite_extinction_width_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_of_dependencies
        dependencies M
    finite_extinction_width_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction width sub-obligation projection follows
the direct surgery-package route selected by the aggregate dependencies.
-/
theorem finite_extinction_width_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_width_subobligations_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_width_subobligations_of_surgery_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the named finite-extinction
sub-obligations and the certificate tying them to the finite-extinction
conclusion.
-/
theorem finite_extinction_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω,
          ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
          ∃ surgery : HasRicciFlowWithSurgery n M,
          ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
          ∃ _finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
          ∃ sweepout :
            HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
          ∃ _sweepoutParameterSpace :
            HasFiniteExtinctionSweepoutParameterSpace M
              _finiteFundamentalGroup,
          ∃ _sweepoutContinuity :
            HasFiniteExtinctionSweepoutContinuity M
              _finiteFundamentalGroup sweepout,
          ∃ _sweepoutAreaBound :
            HasFiniteExtinctionSweepoutAreaBound M
              _finiteFundamentalGroup sweepout,
          ∃ _sweepoutNontriviality :
            HasFiniteExtinctionSweepoutNontriviality M
              _finiteFundamentalGroup sweepout,
          ∃ _areaFunctional :
            HasFiniteExtinctionAreaFunctionalSetup
              flow surgery control _finiteFundamentalGroup sweepout,
          ∃ widthDefinition :
            HasFiniteExtinctionMinMaxWidthDefinition
              flow surgery control _finiteFundamentalGroup sweepout,
          ∃ _widthCompactness :
            HasFiniteExtinctionWidthCompactness
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _widthLowerSemicontinuity :
            HasFiniteExtinctionWidthLowerSemicontinuity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minimizingSequence :
            HasFiniteExtinctionMinimizingSequence
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _pullTightArgument :
            HasFiniteExtinctionPullTightArgument
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minMaxStationarity :
            HasFiniteExtinctionMinMaxStationarity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _minSurfaceRegularity :
            HasFiniteExtinctionMinSurfaceRegularity
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ _positiveWidth :
            HasFiniteExtinctionPositiveWidth
              flow surgery control _finiteFundamentalGroup sweepout
              widthDefinition,
          ∃ widthTheory :
            HasFiniteExtinctionWidthTheory flow surgery control,
          ∃ _firstVariationFormula :
            HasFiniteExtinctionFirstVariationFormula
              flow surgery control widthTheory,
          ∃ _secondVariationInequality :
            HasFiniteExtinctionSecondVariationInequality
              flow surgery control widthTheory,
          ∃ _gaussBonnetEstimate :
            HasFiniteExtinctionGaussBonnetEstimate
              flow surgery control widthTheory,
          ∃ _scalarCurvatureWidthBound :
            HasFiniteExtinctionScalarCurvatureWidthBound
              flow surgery control widthTheory,
          ∃ widthEvolution :
            HasFiniteExtinctionWidthEvolution
              flow surgery control widthTheory,
          ∃ _widthDifferentialInequality :
            HasFiniteExtinctionWidthDifferentialInequality
              flow surgery control widthTheory,
          ∃ _surgeryMetricComparison :
            HasFiniteExtinctionSurgeryMetricComparison
              flow surgery control widthTheory widthEvolution,
          ∃ _surgeryWidthComparisonMap :
            HasFiniteExtinctionSurgeryWidthComparisonMap
              flow surgery control widthTheory widthEvolution,
          ∃ _surgeryWidthDrop :
            HasFiniteExtinctionSurgeryWidthDrop
              flow surgery control widthTheory widthEvolution,
          ∃ surgeryDiscardControl :
            HasFiniteExtinctionSurgeryDiscardControl
              flow surgery control widthTheory widthEvolution,
          ∃ _discardedComponentWidthNeutrality :
            HasFiniteExtinctionDiscardedComponentWidthNeutrality
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _discardedComponentSweepoutTriviality :
            HasFiniteExtinctionDiscardedComponentSweepoutTriviality
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _discardedComponentClassification :
            HasFiniteExtinctionDiscardedComponentClassification
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _survivingComponentTracking :
            HasFiniteExtinctionSurvivingComponentTracking
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ _componentTopology :
            HasFiniteExtinctionComponentTopology
              flow surgery control widthTheory widthEvolution
              surgeryDiscardControl,
          ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
          ∃ _positiveScalarCurvatureLowerBound :
            HasFiniteExtinctionPositiveScalarCurvatureLowerBound
              flow surgery control pinching,
          ∃ _positiveScalarCurvaturePersistence :
            HasFiniteExtinctionPositiveScalarCurvaturePersistence
              flow surgery control pinching,
          ∃ componentControl :
            HasFiniteExtinctionComponentControl flow surgery control pinching,
          ∃ _volumeEvolutionFormula :
            HasFiniteExtinctionVolumeEvolutionFormula
              flow surgery control pinching componentControl,
          ∃ _surgeryVolumeNonincrease :
            HasFiniteExtinctionSurgeryVolumeNonincrease
              flow surgery control pinching componentControl,
          ∃ _scalarCurvatureDifferentialInequality :
            HasFiniteExtinctionScalarCurvatureDifferentialInequality
              flow surgery control pinching componentControl,
          ∃ _volumeDifferentialInequality :
            HasFiniteExtinctionVolumeDifferentialInequality
              flow surgery control pinching componentControl,
          ∃ _volumeDecayEstimate :
            HasFiniteExtinctionVolumeDecayEstimate
              flow surgery control pinching componentControl,
          ∃ timeBound :
            HasFiniteExtinctionTimeBound
              flow surgery control pinching componentControl,
          ∃ _differentialInequalityIntegration :
            HasFiniteExtinctionDifferentialInequalityIntegration
              flow surgery control pinching componentControl timeBound,
          ∃ _finiteTimeIntegration :
            HasFiniteExtinctionFiniteTimeIntegration
              flow surgery control pinching componentControl timeBound,
          ∃ _surgeryTimeSummability :
            HasFiniteExtinctionSurgeryTimeSummability
              flow surgery control pinching componentControl timeBound,
          ∃ _extinctionTimeContradiction :
            HasFiniteExtinctionExtinctionTimeContradiction
              flow surgery control pinching componentControl timeBound,
          ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
          ∃ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
            HasFiniteExtinctionConclusionDerivation
              flow surgery control pinching componentControl timeBound
              derivation extinction := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_subobligations_statement_payload_of_dependencies
      dependencies M with
    ⟨n, flow, surgery, control, _widthStatement,
      _subobligationsStatement, _widthSubobligations, subobligations,
      _packageStatement⟩
  exact ⟨n, flow, surgery, control, subobligations⟩

/--
The dependency-level finite-extinction full sub-obligation projection is
selected from the named finite-extinction sub-obligation statement payload.
-/
theorem finite_extinction_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_of_dependencies
        dependencies M
    finite_extinction_subobligations_of_dependencies dependencies M =
      ⟨payload.choose, payload.choose_spec.choose,
        payload.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction full sub-obligation projection follows
the direct surgery-package route selected by the aggregate dependencies.
-/
theorem finite_extinction_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_subobligations_of_dependencies dependencies M =
      ⟨payload.choose,
        ricci_flow_data_of_surgery_package payload.choose_spec.choose,
        ricci_flow_with_surgery_of_surgery_package payload.choose_spec.choose,
        perelman_singularity_control_of_surgery_package
          payload.choose_spec.choose,
        finite_extinction_subobligations_of_surgery_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/-- A completed dependency package supplies the topology extraction package. -/
theorem topology_package_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ExtinctionTopologyExtractionPackage.{u} :=
  dependencies.topology

/-- The dependency-level topology extraction projection is the stored field. -/
theorem topology_package_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_package_of_dependencies dependencies = dependencies.topology :=
  rfl

/--
The legacy dependency-projection name agrees with the structural aggregate
topology-extraction projection.
-/
theorem topology_package_of_dependencies_to_structural_projection_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_package_of_dependencies dependencies =
      topology_of_poincareProofDependencies dependencies :=
  rfl

/--
A completed dependency package supplies the named post-extinction
classification payload for any finite-extinction input through the
theorem-shaped topology extraction statement.
-/
theorem topology_classification_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyClassificationSubobligationsPayload M extinction := by
  rcases topology_extraction_statement_payload_of_topology_package
      (topology_package_of_dependencies dependencies) M extinction with
    ⟨_topologyStatement, _homeomorphism, _derivationStatement,
      classificationSubobligations, _simplyConnectedRecognition,
      _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
      _assemblyStatement,
      _homeomorphismDerivationStatement⟩
  exact classificationSubobligations

/--
The dependency-level topology classification payload is the classification
field selected by the stored topology package's statement payload.
-/
theorem topology_classification_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_payload_of_dependencies dependencies M extinction =
      (topology_extraction_statement_payload_of_topology_package
        dependencies.topology M extinction).choose_spec.choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
The dependency-level topology classification payload agrees with the direct
classification bridge of the stored topology package.
-/
theorem topology_classification_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_payload_of_dependencies dependencies M extinction =
      topology_classification_subobligations_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies post-extinction topology decomposition
for any finite-extinction input.
-/
theorem topology_decomposition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionTopologyDecomposition M extinction :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨decomposition, _payloadTail⟩ := payload
  decomposition

/--
The dependency-level topology decomposition projection is the decomposition
field selected by the named dependency-level classification payload.
-/
theorem topology_decomposition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_decomposition_of_dependencies dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies reconstruction of the topological
surgery trace represented by the extinction decomposition.
-/
theorem topology_surgery_trace_reconstruction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceReconstruction M extinction
      (topology_decomposition_of_dependencies dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, surgeryTraceReconstruction, _payloadTail⟩ := payload
  surgeryTraceReconstruction

/--
The dependency-level topology surgery-trace reconstruction projection is
selected from the named topology classification payload.
-/
theorem topology_surgery_trace_reconstruction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_surgery_trace_reconstruction_of_dependencies
      dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies handle cancellation for the topological
surgery trace.
-/
theorem topology_surgery_trace_handle_cancellation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSurgeryTraceHandleCancellation M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_surgery_trace_reconstruction_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    surgeryTraceHandleCancellation, _payloadTail⟩ := payload
  surgeryTraceHandleCancellation

/--
The dependency-level topology surgery-trace handle-cancellation projection is
selected from the named topology classification payload.
-/
theorem topology_surgery_trace_handle_cancellation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_surgery_trace_handle_cancellation_of_dependencies
      dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies component classification evidence for
each finite-extinction input.
-/
theorem topology_component_classification_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentClassification M extinction
      (topology_decomposition_of_dependencies dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, componentClassification,
    _payloadTail⟩ := payload
  componentClassification

/--
The dependency-level topology component-classification projection is selected
from the named topology classification payload.
-/
theorem topology_component_classification_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_component_classification_of_dependencies dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies homeomorphism classification for
discarded extinction components.
-/
theorem topology_discarded_component_homeomorphism_classification_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionDiscardedComponentHomeomorphismClassification M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_component_classification_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    discardedComponentHomeomorphismClassification, _payloadTail⟩ := payload
  discardedComponentHomeomorphismClassification

/--
The dependency-level discarded-component homeomorphism classification
projection is selected from the named topology classification payload.
-/
theorem topology_discarded_component_homeomorphism_classification_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_discarded_component_homeomorphism_classification_of_dependencies
      dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose_spec.choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the post-extinction component inventory.
-/
theorem topology_component_inventory_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentInventory M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_component_classification_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, componentInventory,
    _payloadTail⟩ := payload
  componentInventory

/--
The dependency-level topology component-inventory projection is selected from
the named topology classification payload.
-/
theorem topology_component_inventory_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_component_inventory_of_dependencies dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies boundary-sphere control for extinction
components.
-/
theorem topology_component_boundary_sphere_control_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionComponentBoundarySphereControl M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_component_classification_of_dependencies
        dependencies M extinction)
      (topology_component_inventory_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    componentBoundarySphereControl, _payloadTail⟩ := payload
  componentBoundarySphereControl

/--
The dependency-level topology component boundary-sphere control projection is
selected from the named topology classification payload.
-/
theorem topology_component_boundary_sphere_control_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_component_boundary_sphere_control_of_dependencies
      dependencies M extinction =
      (topology_classification_payload_of_dependencies
        dependencies M extinction).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the 3-sphere recognition input for each
target manifold.
-/
theorem three_sphere_recognition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasThreeSphereRecognition M
      (fun extinction =>
        topology_decomposition_of_dependencies dependencies M extinction) :=
  three_sphere_recognition_of_topology_package
    (topology_package_of_dependencies dependencies) M

/--
The dependency-level 3-sphere recognition projection is the topology-package
projection through the stored topology package.
-/
theorem three_sphere_recognition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    three_sphere_recognition_of_dependencies dependencies M =
      three_sphere_recognition_of_topology_package
        (topology_package_of_dependencies dependencies) M := by
  apply Subsingleton.elim

/--
A completed dependency package supplies prime-decomposition evidence for each
finite-extinction input.
-/
theorem topology_prime_decomposition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecomposition M extinction
      (topology_decomposition_of_dependencies dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, primeDecomposition, _payloadTail⟩ :=
      payload
  primeDecomposition

/--
The dependency-level topology prime-decomposition projection is selected from
the named topology classification payload.
-/
theorem topology_prime_decomposition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_prime_decomposition_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, primeDecomposition,
          _payloadTail⟩ := payload
        exact primeDecomposition) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies existence of the prime decomposition
used after extinction.
-/
theorem topology_prime_decomposition_existence_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionExistence M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    primeDecompositionExistence, _payloadTail⟩ := payload
  primeDecompositionExistence

/--
The dependency-level topology prime-decomposition existence projection is
selected from the named topology classification payload.
-/
theorem topology_prime_decomposition_existence_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_prime_decomposition_existence_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          primeDecompositionExistence, _payloadTail⟩ := payload
        exact primeDecompositionExistence) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the sphere-theorem input behind the
prime decomposition.
-/
theorem topology_sphere_theorem_application_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphereTheoremApplication M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, sphereTheoremApplication, _payloadTail⟩ :=
      payload
  sphereTheoremApplication

/--
The dependency-level topology sphere-theorem projection is selected from the
named topology classification payload.
-/
theorem topology_sphere_theorem_application_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_sphere_theorem_application_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, sphereTheoremApplication,
          _payloadTail⟩ := payload
        exact sphereTheoremApplication) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies embedded spheres realizing the prime
decomposition cuts.
-/
theorem topology_embedded_sphere_production_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionEmbeddedSphereProduction M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_sphere_theorem_application_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    embeddedSphereProduction, _payloadTail⟩ := payload
  embeddedSphereProduction

/--
The dependency-level topology embedded-sphere production projection is selected
from the named topology classification payload.
-/
theorem topology_embedded_sphere_production_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_embedded_sphere_production_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          embeddedSphereProduction, _payloadTail⟩ := payload
        exact embeddedSphereProduction) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies loop-theorem control for the prime
decomposition cuts.
-/
theorem topology_loop_theorem_application_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionLoopTheoremApplication M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_sphere_theorem_application_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, loopTheoremApplication, _payloadTail⟩ :=
      payload
  loopTheoremApplication

/--
The dependency-level topology loop-theorem projection is selected from the named
topology classification payload.
-/
theorem topology_loop_theorem_application_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_loop_theorem_application_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, loopTheoremApplication, _payloadTail⟩ :=
            payload
        exact loopTheoremApplication) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies prime-decomposition compatibility for
each finite-extinction input.
-/
theorem topology_prime_decomposition_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeDecompositionCompatibility M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_component_classification_of_dependencies
        dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    primeDecompositionCompatibility, _payloadTail⟩ := payload
  primeDecompositionCompatibility

/--
The dependency-level topology prime-decomposition compatibility projection is
selected from the named topology classification payload.
-/
theorem topology_prime_decomposition_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_prime_decomposition_compatibility_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          primeDecompositionCompatibility, _payloadTail⟩ := payload
        exact primeDecompositionCompatibility) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies uniqueness of the selected prime
factors.
-/
theorem topology_prime_factor_uniqueness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionPrimeFactorUniqueness M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_component_classification_of_dependencies
        dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_prime_decomposition_compatibility_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, primeFactorUniqueness,
    _payloadTail⟩ := payload
  primeFactorUniqueness

/--
The dependency-level topology prime-factor uniqueness projection is selected
from the named topology classification payload.
-/
theorem topology_prime_factor_uniqueness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_prime_factor_uniqueness_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, primeFactorUniqueness,
          _payloadTail⟩ := payload
        exact primeFactorUniqueness) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies irreducibility evidence for each
finite-extinction input.
-/
theorem topology_irreducibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibility M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, irreducibility,
    _payloadTail⟩ := payload
  irreducibility

/--
The dependency-level topology irreducibility projection is selected from the
named topology classification payload.
-/
theorem topology_irreducibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_irreducibility_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          irreducibility, _payloadTail⟩ := payload
        exact irreducibility) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies recognition of the irreducible factors.
-/
theorem topology_irreducible_factor_recognition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionIrreducibleFactorRecognition M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    irreducibleFactorRecognition, _payloadTail⟩ := payload
  irreducibleFactorRecognition

/--
The dependency-level topology irreducible-factor recognition projection is
selected from the named topology classification payload.
-/
theorem topology_irreducible_factor_recognition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_irreducible_factor_recognition_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, irreducibleFactorRecognition, _payloadTail⟩ :=
            payload
        exact irreducibleFactorRecognition) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies connected-sum collapse evidence for
each finite-extinction input.
-/
theorem topology_connected_sum_collapse_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumCollapse M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, connectedSumCollapse, _payloadTail⟩ :=
      payload
  connectedSumCollapse

/--
The dependency-level topology connected-sum collapse projection is selected
from the named topology classification payload.
-/
theorem topology_connected_sum_collapse_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_connected_sum_collapse_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, connectedSumCollapse,
          _payloadTail⟩ := payload
        exact connectedSumCollapse) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies fundamental-group control for
connected-sum collapse.
-/
theorem topology_connected_sum_fundamental_group_control_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumFundamentalGroupControl M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    connectedSumFundamentalGroupControl, _payloadTail⟩ := payload
  connectedSumFundamentalGroupControl

/--
The dependency-level topology connected-sum fundamental-group control
projection is selected from the named topology classification payload.
-/
theorem topology_connected_sum_fundamental_group_control_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_connected_sum_fundamental_group_control_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          connectedSumFundamentalGroupControl, _payloadTail⟩ := payload
        exact connectedSumFundamentalGroupControl) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the van Kampen calculation for
connected-sum fundamental groups.
-/
theorem topology_connected_sum_van_kampen_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionConnectedSumVanKampenCalculation M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_fundamental_group_control_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, connectedSumVanKampen,
    _payloadTail⟩ := payload
  connectedSumVanKampen

/--
The dependency-level topology connected-sum van Kampen projection is selected
from the named topology classification payload.
-/
theorem topology_connected_sum_van_kampen_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_connected_sum_van_kampen_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, connectedSumVanKampen,
          _payloadTail⟩ := payload
        exact connectedSumVanKampen) := by
  apply Subsingleton.elim

/--
A completed dependency package forces the surviving prime factor to be simply
connected.
-/
theorem topology_simply_connected_prime_factor_control_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSimplyConnectedPrimeFactorControl M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_fundamental_group_control_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    simplyConnectedPrimeFactorControl, _payloadTail⟩ := payload
  simplyConnectedPrimeFactorControl

/--
The dependency-level topology simply connected prime-factor control projection
is selected from the named topology classification payload.
-/
theorem topology_simply_connected_prime_factor_control_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_prime_factor_control_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          simplyConnectedPrimeFactorControl, _payloadTail⟩ := payload
        exact simplyConnectedPrimeFactorControl) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies spherical-space-form reduction evidence
for each finite-extinction input.
-/
theorem topology_spherical_space_form_reduction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionSphericalSpaceFormReduction M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, sphericalReduction, _payloadTail⟩ :=
      payload
  sphericalReduction

/--
The dependency-level topology spherical-space-form reduction projection is
selected from the named topology classification payload.
-/
theorem topology_spherical_space_form_reduction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_space_form_reduction_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, sphericalReduction,
          _payloadTail⟩ := payload
        exact sphericalReduction) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies spherical-space-form classification
evidence for each finite-extinction input.
-/
theorem topology_spherical_space_form_classification_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormClassification M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    sphericalClassification, _payloadTail⟩ := payload
  sphericalClassification

/--
The dependency-level topology spherical-space-form classification projection
is selected from the named topology classification payload.
-/
theorem topology_spherical_space_form_classification_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_space_form_classification_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          sphericalClassification, _payloadTail⟩ := payload
        exact sphericalClassification) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies spherical quotient model evidence for
each finite-extinction input.
-/
theorem topology_spherical_quotient_model_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormQuotientModel M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, quotientModel, _payloadTail⟩ := payload
  quotientModel

/--
The dependency-level topology spherical quotient-model projection is selected
from the named topology classification payload.
-/
theorem topology_spherical_quotient_model_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_quotient_model_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, quotientModel, _payloadTail⟩ := payload
        exact quotientModel) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the free action behind the spherical
quotient model.
-/
theorem topology_spherical_free_action_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFreeAction M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, sphericalFreeAction,
    _payloadTail⟩ := payload
  sphericalFreeAction

/--
The dependency-level topology spherical free-action projection is selected from
the named topology classification payload.
-/
theorem topology_spherical_free_action_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_free_action_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, sphericalFreeAction,
          _payloadTail⟩ := payload
        exact sphericalFreeAction) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the spherical universal-cover input for
each finite-extinction input.
-/
theorem topology_spherical_universal_cover_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormUniversalCover M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    universalCover, _payloadTail⟩ := payload
  universalCover

/--
The dependency-level topology spherical universal-cover projection is selected
from the named topology classification payload.
-/
theorem topology_spherical_universal_cover_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_universal_cover_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          universalCover, _payloadTail⟩ := payload
        exact universalCover) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the covering model connecting the
spherical quotient to its universal cover.
-/
theorem topology_spherical_covering_model_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringModel M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_universal_cover_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, sphericalCoveringModel, _payloadTail⟩ := payload
  sphericalCoveringModel

/--
The dependency-level topology spherical covering-model projection is selected
from the named topology classification payload.
-/
theorem topology_spherical_covering_model_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_covering_model_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, sphericalCoveringModel, _payloadTail⟩ := payload
        exact sphericalCoveringModel) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the covering projection from the
universal cover to the spherical quotient.
-/
theorem topology_spherical_covering_projection_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormCoveringProjection M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_universal_cover_of_dependencies
        dependencies M extinction)
      (topology_spherical_covering_model_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, sphericalCoveringProjection,
    _payloadTail⟩ := payload
  sphericalCoveringProjection

/--
The dependency-level topology spherical covering-projection projection is
selected from the named topology classification payload.
-/
theorem topology_spherical_covering_projection_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_covering_projection_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          sphericalCoveringProjection, _payloadTail⟩ := payload
        exact sphericalCoveringProjection) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the spherical-space-form fundamental
group computation for each finite-extinction input.
-/
theorem topology_spherical_fundamental_group_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormFundamentalGroupComputation M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    fundamentalGroupComputation, _payloadTail⟩ := payload
  fundamentalGroupComputation

/--
The dependency-level topology spherical fundamental-group computation
projection is selected from the named topology classification payload.
-/
theorem topology_spherical_fundamental_group_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_fundamental_group_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, fundamentalGroupComputation,
          _payloadTail⟩ := payload
        exact fundamentalGroupComputation) := by
  apply Subsingleton.elim

/--
A completed dependency package identifies the deck group with the computed
fundamental group for each finite-extinction input.
-/
theorem topology_deck_group_identification_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupIdentification M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, deckGroupIdentification, _payloadTail⟩ :=
      payload
  deckGroupIdentification

/--
The dependency-level topology deck-group identification projection is selected
from the named topology classification payload.
-/
theorem topology_deck_group_identification_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_deck_group_identification_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          deckGroupIdentification, _payloadTail⟩ := payload
        exact deckGroupIdentification) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies properness and freeness of the
spherical deck action.
-/
theorem topology_deck_action_properness_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionProperness M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    deckActionProperness, _payloadTail⟩ := payload
  deckActionProperness

/--
The dependency-level topology deck-action properness projection is selected
from the named topology classification payload.
-/
theorem topology_deck_action_properness_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_deck_action_properness_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, deckActionProperness, _payloadTail⟩ :=
            payload
        exact deckActionProperness) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies deck-group triviality for each
finite-extinction input.
-/
theorem topology_deck_group_triviality_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckGroupTriviality M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, deckGroupTriviality, _payloadTail⟩ := payload
  deckGroupTriviality

/--
The dependency-level topology deck-group triviality projection is selected from
the named topology classification payload.
-/
theorem topology_deck_group_triviality_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_deck_group_triviality_of_dependencies dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          deckGroupTriviality, _payloadTail⟩ := payload
        exact deckGroupTriviality) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies trivialization of the spherical
space-form deck action.
-/
theorem topology_deck_action_trivialization_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormDeckActionTrivialization M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, deckActionTrivialization,
    _payloadTail⟩ := payload
  deckActionTrivialization

/--
The dependency-level topology deck-action trivialization projection is selected
from the named topology classification payload.
-/
theorem topology_deck_action_trivialization_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_deck_action_trivialization_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, deckActionTrivialization, _payloadTail⟩ :=
            payload
        exact deckActionTrivialization) := by
  apply Subsingleton.elim

/--
A completed dependency package identifies the quotient by a trivial deck action
with the cover.
-/
theorem topology_trivial_deck_quotient_identification_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialDeckQuotientIdentification M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction)
      (topology_deck_action_trivialization_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, _deckActionTrivialization,
    trivialDeckQuotientIdentification, _payloadTail⟩ := payload
  trivialDeckQuotientIdentification

/--
The dependency-level topology trivial deck-quotient identification projection
is selected from the named topology classification payload.
-/
theorem topology_trivial_deck_quotient_identification_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_trivial_deck_quotient_identification_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, _deckActionTrivialization,
          trivialDeckQuotientIdentification, _payloadTail⟩ := payload
        exact trivialDeckQuotientIdentification) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies simply connected recognition evidence
for each finite-extinction input.
-/
theorem topology_simply_connected_recognition_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSimplyConnectedExtinctionRecognition M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, _deckActionTrivialization,
    _trivialDeckQuotientIdentification, _trivialQuotient,
    _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
    simplyConnectedRecognition⟩ := payload
  simplyConnectedRecognition

/--
The dependency-level topology simply connected recognition projection is
selected from the named topology classification payload.
-/
theorem topology_simply_connected_recognition_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, _deckActionTrivialization,
          _trivialDeckQuotientIdentification, _trivialQuotient,
          _trivialQuotientHomeomorphism, _sphericalHomeomorphismLift,
          simplyConnectedRecognition⟩ := payload
        exact simplyConnectedRecognition) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the trivial spherical quotient input for
each finite-extinction input.
-/
theorem topology_trivial_spherical_quotient_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasTrivialSphericalSpaceFormQuotient M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, _deckActionTrivialization,
    _trivialDeckQuotientIdentification, trivialQuotient, _payloadTail⟩ :=
      payload
  trivialQuotient

/--
The dependency-level topology trivial spherical quotient projection is selected
from the named topology classification payload.
-/
theorem topology_trivial_spherical_quotient_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_trivial_spherical_quotient_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, _deckActionTrivialization,
          _trivialDeckQuotientIdentification, trivialQuotient,
          _payloadTail⟩ := payload
        exact trivialQuotient) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the homeomorphism input produced by the
trivial spherical quotient.
-/
theorem topology_trivial_quotient_homeomorphism_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormTrivialQuotientHomeomorphism M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_universal_cover_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction)
      (topology_trivial_spherical_quotient_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, _deckActionTrivialization,
    _trivialDeckQuotientIdentification, _trivialQuotient,
    trivialQuotientHomeomorphism, _payloadTail⟩ := payload
  trivialQuotientHomeomorphism

/--
The dependency-level topology trivial-quotient homeomorphism projection is
selected from the named topology classification payload.
-/
theorem topology_trivial_quotient_homeomorphism_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_trivial_quotient_homeomorphism_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, _deckActionTrivialization,
          _trivialDeckQuotientIdentification, _trivialQuotient,
          trivialQuotientHomeomorphism, _payloadTail⟩ := payload
        exact trivialQuotientHomeomorphism) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the homeomorphism lift through the
trivial spherical quotient.
-/
theorem topology_spherical_homeomorphism_lift_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasSphericalSpaceFormHomeomorphismLift M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_universal_cover_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction)
      (topology_trivial_spherical_quotient_of_dependencies
        dependencies M extinction)
      (topology_trivial_quotient_homeomorphism_of_dependencies
        dependencies M extinction) :=
  let payload :=
    topology_classification_payload_of_dependencies dependencies M extinction
  let ⟨_decomposition, _surgeryTraceReconstruction,
    _surgeryTraceHandleCancellation, _componentClassification,
    _discardedComponentHomeomorphismClassification, _componentInventory,
    _componentBoundarySphereControl, _primeDecomposition,
    _primeDecompositionExistence, _sphereTheoremApplication,
    _embeddedSphereProduction, _loopTheoremApplication,
    _primeDecompositionCompatibility, _primeFactorUniqueness, _irreducibility,
    _irreducibleFactorRecognition, _connectedSumCollapse,
    _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
    _simplyConnectedPrimeFactorControl, _sphericalReduction,
    _sphericalClassification, _quotientModel, _sphericalFreeAction,
    _universalCover, _sphericalCoveringModel, _sphericalCoveringProjection,
    _fundamentalGroupComputation, _deckGroupIdentification,
    _deckActionProperness, _deckGroupTriviality, _deckActionTrivialization,
    _trivialDeckQuotientIdentification, _trivialQuotient,
    _trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
    _payloadTail⟩ := payload
  sphericalHomeomorphismLift

/--
The dependency-level topology spherical homeomorphism-lift projection is
selected from the named topology classification payload.
-/
theorem topology_spherical_homeomorphism_lift_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_classification_payload_of_dependencies dependencies M
            extinction
        let ⟨_decomposition, _surgeryTraceReconstruction,
          _surgeryTraceHandleCancellation, _componentClassification,
          _discardedComponentHomeomorphismClassification, _componentInventory,
          _componentBoundarySphereControl, _primeDecomposition,
          _primeDecompositionExistence, _sphereTheoremApplication,
          _embeddedSphereProduction, _loopTheoremApplication,
          _primeDecompositionCompatibility, _primeFactorUniqueness,
          _irreducibility, _irreducibleFactorRecognition, _connectedSumCollapse,
          _connectedSumFundamentalGroupControl, _connectedSumVanKampen,
          _simplyConnectedPrimeFactorControl, _sphericalReduction,
          _sphericalClassification, _quotientModel, _sphericalFreeAction,
          _universalCover, _sphericalCoveringModel,
          _sphericalCoveringProjection, _fundamentalGroupComputation,
          _deckGroupIdentification, _deckActionProperness,
          _deckGroupTriviality, _deckActionTrivialization,
          _trivialDeckQuotientIdentification, _trivialQuotient,
          _trivialQuotientHomeomorphism, sphericalHomeomorphismLift,
          _payloadTail⟩ := payload
        exact sphericalHomeomorphismLift) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the theorem-shaped topology extraction
statement together with the final extraction interface consumed by the assembly
layer.
-/
theorem topology_extraction_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _topologyStatement : ExtinctionTopologyExtractionStatement.{u},
      ExtinctionImpliesSphereStatement.{u} := by
  rcases topology_extraction_payload_of_topology_package
      (topology_package_of_dependencies dependencies) with
    ⟨topologyStatement, extraction⟩
  exact ⟨topologyStatement, extraction⟩

/--
The dependency-level topology extraction payload is the corresponding payload
of the stored topology package.
-/
theorem topology_extraction_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_payload_of_dependencies dependencies =
      topology_extraction_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level topology extraction payload follows the stored topology
package route.
-/
theorem topology_extraction_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_payload_of_dependencies dependencies =
      topology_extraction_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
A completed dependency package extracts the theorem-shaped topology statement,
its final homeomorphism, the full classification sub-obligation stack, the
simply-connected recognition statement, the spherical trivial-quotient
statement, the spherical homeomorphism-lift statement, and the
fixed-homeomorphism derivation statements from any finite-extinction input.
-/
theorem topology_extraction_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
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
    ∃ _simplyConnectedRecognition :
      ExtinctionTopologySimplyConnectedRecognitionStatement M extinction,
    ∃ _sphericalTrivialQuotient :
      ExtinctionTopologySphericalTrivialQuotientStatement M extinction,
    ∃ _sphericalHomeomorphismLift :
      ExtinctionTopologySphericalHomeomorphismLiftStatement M extinction,
    ∃ _assemblyStatement :
      ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
        homeomorphism,
      ExtinctionTopologyHomeomorphismDerivationStatement M extinction
        homeomorphism := by
  rcases topology_extraction_statement_payload_of_topology_package
      (topology_package_of_dependencies dependencies) M extinction with
    ⟨topologyStatement, homeomorphism, derivationStatement,
      classificationSubobligations, simplyConnectedRecognition,
      sphericalTrivialQuotient, sphericalHomeomorphismLift, assemblyStatement,
      homeomorphismDerivationStatement⟩
  exact ⟨topologyStatement, homeomorphism, derivationStatement,
    classificationSubobligations, simplyConnectedRecognition,
    sphericalTrivialQuotient, sphericalHomeomorphismLift, assemblyStatement,
    homeomorphismDerivationStatement⟩

/--
The dependency-level topology statement payload is the corresponding payload of
the stored topology package.
-/
theorem topology_extraction_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      topology_extraction_statement_payload_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload follows the stored
topology package route.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      topology_extraction_statement_payload_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the full post-extinction classification
sub-obligation stack through the theorem-shaped extraction payload.
-/
theorem topology_classification_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
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
  exact topology_classification_payload_of_dependencies dependencies M
    extinction

/--
The explicit dependency-level classification sub-obligation projection is the
named dependency-level classification payload.
-/
theorem topology_classification_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      topology_classification_payload_of_dependencies
        dependencies M extinction := by
  apply Subsingleton.elim

/--
The dependency-level topology classification sub-obligation projection agrees
with the direct topology-package classification bridge.
-/
theorem topology_classification_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
        dependencies M extinction =
      topology_classification_subobligations_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the simply-connected recognition
substatement through the stored topology package.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySimplyConnectedRecognitionStatement M extinction :=
  topology_simply_connected_recognition_statement_of_topology_package
    dependencies.topology M extinction

/--
The dependency-level simply-connected recognition substatement is the direct
projection from the stored topology package.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition substatement agrees with the
direct topology-package route.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
        dependencies M extinction =
      topology_simply_connected_recognition_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the spherical trivial-quotient
substatement through the stored topology package.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalTrivialQuotientStatement M extinction :=
  topology_spherical_trivial_quotient_statement_of_topology_package
    dependencies.topology M extinction

/--
The dependency-level spherical trivial-quotient substatement is the direct
projection from the stored topology package.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient substatement agrees with the
direct topology-package route.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
        dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the spherical homeomorphism-lift
substatement through the stored topology package.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalHomeomorphismLiftStatement M extinction :=
  topology_spherical_homeomorphism_lift_statement_of_topology_package
    dependencies.topology M extinction

/--
The dependency-level spherical homeomorphism-lift substatement is the direct
projection from the stored topology package.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift substatement agrees with the
direct topology-package route.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
        dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package extracts the final homeomorphism from any
finite-extinction input.
-/
theorem topology_derivation_statement_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ∃ homeomorphism : Nonempty (M ≃ₜ ThreeSphere),
      ExtinctionTopologyDerivationStatement M extinction homeomorphism :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, homeomorphism, derivationStatement,
        _classificationSubobligations, _simplyConnectedRecognition,
        _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
        _assemblyStatement,
        _homeomorphismDerivationStatement⟩
    exact ⟨homeomorphism, derivationStatement⟩

/--
The dependency-level topology derivation payload is the derivation payload of
the dependency-level topology extraction statement.
-/
theorem topology_derivation_statement_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_dependencies
      dependencies M extinction =
      topology_derivation_statement_payload_of_extraction_statement
        (extinction_topology_extraction_statement_of_topology_package
          dependencies.topology)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation payload follows the theorem-shaped
statement selected by the stored topology package.
-/
theorem topology_derivation_statement_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_dependencies
      dependencies M extinction =
      topology_derivation_statement_payload_of_extraction_statement
        (extinction_topology_extraction_statement_of_topology_package
          dependencies.topology)
        M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package extracts the final homeomorphism from the
theorem-shaped topology extraction statement payload.
-/
theorem homeomorphism_of_extinction_and_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  rcases topology_derivation_statement_payload_of_dependencies
      dependencies M extinction with
    ⟨homeomorphism, _derivationStatement⟩
  exact homeomorphism

/--
The dependency-level extinction-to-sphere homeomorphism is selected from the
named topology derivation-statement payload.
-/
theorem homeomorphism_of_extinction_and_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_extinction_and_dependencies dependencies M extinction =
      (topology_derivation_statement_payload_of_dependencies
        dependencies M extinction).choose := by
  apply Subsingleton.elim

/--
The dependency-level extinction-to-sphere homeomorphism agrees with the
homeomorphism selected by the stored topology package.
-/
theorem homeomorphism_of_extinction_and_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_extinction_and_dependencies dependencies M extinction =
      homeomorphism_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level topology extraction payload also supplies the derivation
statement for the projected dependency-level homeomorphism.
-/
theorem topology_derivation_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) := by
  rcases topology_derivation_statement_payload_of_dependencies
      dependencies M extinction with
    ⟨homeomorphism, derivationStatement⟩
  convert derivationStatement

/--
The dependency-level topology derivation statement is selected from the named
topology derivation-statement payload.
-/
theorem topology_derivation_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        let payload :=
          topology_derivation_statement_payload_of_dependencies
            dependencies M extinction
        convert payload.choose_spec) := by
  apply Subsingleton.elim

/--
The theorem-shaped dependency extraction route supplies the homeomorphism
assembly statement for the projected dependency-level homeomorphism.
-/
theorem topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, homeomorphism, _derivationStatement,
        _classificationSubobligations, _simplyConnectedRecognition,
        _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
        assemblyStatement,
        _homeomorphismDerivationStatement⟩
    convert assemblyStatement

/--
The dependency-level topology homeomorphism assembly statement is selected from
the named topology extraction statement payload.
-/
theorem topology_homeomorphism_assembly_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            _classificationSubobligations, _simplyConnectedRecognition,
            _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
            assemblyStatement,
            _homeomorphismDerivationStatement⟩
        convert assemblyStatement) := by
  apply Subsingleton.elim

/--
The theorem-shaped dependency extraction route supplies the simply-connected
recognition statement from the topology extraction payload.
-/
theorem topology_simply_connected_recognition_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySimplyConnectedRecognitionStatement M extinction :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, _homeomorphism, _derivationStatement,
        _classificationSubobligations, simplyConnectedRecognition,
        _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
        _assemblyStatement,
        _homeomorphismDerivationStatement⟩
    exact simplyConnectedRecognition

/--
The dependency-level simply-connected recognition statement is selected from
the named topology extraction statement payload.
-/
theorem topology_simply_connected_recognition_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            _classificationSubobligations, simplyConnectedRecognition,
            _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
            _assemblyStatement,
            _homeomorphismDerivationStatement⟩
        exact simplyConnectedRecognition) := by
  apply Subsingleton.elim

/--
The theorem-shaped dependency extraction route supplies the spherical
trivial-quotient statement from the topology extraction payload.
-/
theorem topology_spherical_trivial_quotient_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalTrivialQuotientStatement M extinction :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, _homeomorphism, _derivationStatement,
        _classificationSubobligations, _simplyConnectedRecognition,
        sphericalTrivialQuotient,
        _sphericalHomeomorphismLift, _assemblyStatement,
        _homeomorphismDerivationStatement⟩
    exact sphericalTrivialQuotient

/--
The dependency-level spherical trivial-quotient statement is selected from the
named topology extraction statement payload.
-/
theorem topology_spherical_trivial_quotient_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            _classificationSubobligations, _simplyConnectedRecognition,
            sphericalTrivialQuotient,
            _sphericalHomeomorphismLift, _assemblyStatement,
            _homeomorphismDerivationStatement⟩
        exact sphericalTrivialQuotient) := by
  apply Subsingleton.elim

/--
The theorem-shaped dependency extraction route supplies the spherical
homeomorphism-lift statement from the topology extraction payload.
-/
theorem topology_spherical_homeomorphism_lift_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalHomeomorphismLiftStatement M extinction :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, _homeomorphism, _derivationStatement,
        _classificationSubobligations, _simplyConnectedRecognition,
        _sphericalTrivialQuotient, sphericalHomeomorphismLift,
        _assemblyStatement, _homeomorphismDerivationStatement⟩
    exact sphericalHomeomorphismLift

/--
The dependency-level spherical homeomorphism-lift statement is selected from
the named topology extraction statement payload.
-/
theorem topology_spherical_homeomorphism_lift_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            _classificationSubobligations, _simplyConnectedRecognition,
            _sphericalTrivialQuotient, sphericalHomeomorphismLift,
            _assemblyStatement, _homeomorphismDerivationStatement⟩
        exact sphericalHomeomorphismLift) := by
  apply Subsingleton.elim

/--
The theorem-shaped dependency extraction route supplies the homeomorphism
derivation statement for the projected dependency-level homeomorphism.
-/
theorem topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) :=
  by
    rcases topology_extraction_statement_payload_of_dependencies
        dependencies M extinction with
      ⟨_topologyStatement, homeomorphism, _derivationStatement,
        _classificationSubobligations, _simplyConnectedRecognition,
        _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
        _assemblyStatement,
        homeomorphismDerivationStatement⟩
    convert homeomorphismDerivationStatement

/--
The dependency-level topology homeomorphism derivation statement is selected
from the named topology extraction statement payload.
-/
theorem topology_homeomorphism_derivation_statement_via_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            _classificationSubobligations, _simplyConnectedRecognition,
            _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
            _assemblyStatement,
            homeomorphismDerivationStatement⟩
        convert homeomorphismDerivationStatement) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the homeomorphism assembly certificate
from the post-extinction classification data.
-/
theorem topology_homeomorphism_assembly_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismAssembly M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction)
      (topology_simply_connected_recognition_of_dependencies
        dependencies M extinction)
      (topology_trivial_spherical_quotient_of_dependencies
        dependencies M extinction)
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) := by
  rcases topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
      dependencies M extinction with
    ⟨decomposition, primeDecomposition, irreducibility, connectedSumCollapse,
      sphericalReduction, quotientModel, fundamentalGroupComputation,
      deckGroupIdentification, deckGroupTriviality, simplyConnectedRecognition,
      trivialQuotient, homeomorphismAssembly⟩
  convert homeomorphismAssembly

/--
The dependency-level homeomorphism assembly certificate is selected from the
theorem-shaped topology extraction assembly statement.
-/
theorem topology_homeomorphism_assembly_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
            dependencies M extinction with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the derivation certificate for the
projected extinction-to-sphere homeomorphism.
-/
theorem topology_homeomorphism_derivation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionHomeomorphismDerivation M extinction
      (topology_decomposition_of_dependencies dependencies M extinction)
      (topology_prime_decomposition_of_dependencies
        dependencies M extinction)
      (topology_irreducibility_of_dependencies
        dependencies M extinction)
      (topology_connected_sum_collapse_of_dependencies
        dependencies M extinction)
      (topology_spherical_space_form_reduction_of_dependencies
        dependencies M extinction)
      (topology_spherical_fundamental_group_of_dependencies
        dependencies M extinction)
      (topology_deck_group_triviality_of_dependencies
        dependencies M extinction)
      (topology_simply_connected_recognition_of_dependencies
        dependencies M extinction)
      (topology_spherical_quotient_model_of_dependencies
        dependencies M extinction)
      (topology_deck_group_identification_of_dependencies
        dependencies M extinction)
      (topology_trivial_spherical_quotient_of_dependencies
        dependencies M extinction)
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction)
      (topology_homeomorphism_assembly_of_dependencies
        dependencies M extinction) := by
  rcases topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
      dependencies M extinction with
    ⟨decomposition, primeDecomposition, irreducibility, connectedSumCollapse,
      sphericalReduction, fundamentalGroupComputation, deckGroupTriviality,
      simplyConnectedRecognition, quotientModel, deckGroupIdentification,
      trivialQuotient, homeomorphismAssembly, homeomorphismDerivation⟩
  convert homeomorphismDerivation

/--
The dependency-level homeomorphism derivation certificate is selected from the
theorem-shaped topology extraction derivation statement.
-/
theorem topology_homeomorphism_derivation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
            dependencies M extinction with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
A completed dependency package assembles the fixed-manifold topology derivation
statement for the theorem-shaped dependency-level homeomorphism.
-/
theorem topology_derivation_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) :=
  topology_derivation_statement_via_extraction_of_dependencies
    dependencies M extinction

/--
The dependency-level topology derivation statement is the named statement
projection of the topology extraction route.
-/
theorem topology_derivation_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_dependencies dependencies M extinction =
      topology_derivation_statement_via_extraction_of_dependencies
        dependencies M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the statement-mediated homeomorphism
assembly stack extracted from the fixed topology derivation statement.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismAssemblyStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) :=
  topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
    dependencies M extinction

/--
The dependency-level topology homeomorphism assembly statement is the named
assembly-statement projection of the topology extraction route.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
        dependencies M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the statement-mediated homeomorphism
derivation stack extracted from the fixed topology derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) :=
  topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
    dependencies M extinction

/--
The dependency-level topology homeomorphism derivation statement is the named
derivation-statement projection of the topology extraction route.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
        dependencies M extinction := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the theorem-shaped post-extinction
topology extraction statement.
-/
theorem topology_extraction_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ExtinctionTopologyExtractionStatement.{u} := by
  rcases topology_extraction_payload_of_dependencies dependencies with
    ⟨topologyStatement, _extraction⟩
  exact topologyStatement

/--
The dependency-level topology extraction statement is the statement projection
of the stored topology package.
-/
theorem topology_extraction_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_statement_of_dependencies dependencies =
      extinction_topology_extraction_statement_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level theorem-shaped topology statement follows the stored
topology package route.
-/
theorem topology_extraction_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_statement_of_dependencies dependencies =
      extinction_topology_extraction_statement_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level topology extraction payload is the dependency-level
theorem-shaped topology statement paired with its statement-mediated final
extractor.
-/
theorem topology_extraction_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_payload_of_dependencies dependencies =
      ⟨topology_extraction_statement_of_dependencies dependencies,
        extinction_implies_sphere_of_topology_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)⟩ := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload is selected by
destructuring the dependency-level theorem-shaped topology statement.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      (by
        let topologyStatement :=
          topology_extraction_statement_of_dependencies dependencies
        rcases topology_derivation_statement_payload_of_extraction_statement
            topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        let classificationSubobligations :=
          topology_classification_subobligations_of_derivation_statement M
            extinction homeomorphism derivationStatement
        let simplyConnectedRecognition :=
          topology_simply_connected_recognition_statement_of_derivation_statement
            M extinction homeomorphism derivationStatement
        let sphericalTrivialQuotient :=
          topology_spherical_trivial_quotient_statement_of_derivation_statement
            M extinction homeomorphism derivationStatement
        let sphericalHomeomorphismLift :=
          topology_spherical_homeomorphism_lift_statement_of_derivation_statement
            M extinction homeomorphism derivationStatement
        exact ⟨topologyStatement, homeomorphism, derivationStatement,
          classificationSubobligations, simplyConnectedRecognition,
          sphericalTrivialQuotient, sphericalHomeomorphismLift,
          topology_homeomorphism_assembly_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement,
          topology_homeomorphism_derivation_statement_of_derivation_statement M
            extinction homeomorphism derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload can be rebuilt directly
from the dependency-level theorem-shaped topology statement and its named
extraction-statement projection bridges.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_extraction_statement_projections_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      (by
        let topologyStatement :=
          topology_extraction_statement_of_dependencies dependencies
        exact ⟨topologyStatement,
          homeomorphism_of_topology_extraction_statement
            topologyStatement M extinction,
          topology_derivation_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_classification_subobligations_of_extraction_statement
            topologyStatement M extinction,
          topology_simply_connected_recognition_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_spherical_trivial_quotient_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_spherical_homeomorphism_lift_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_homeomorphism_assembly_statement_of_extraction_statement
            topologyStatement M extinction,
          topology_homeomorphism_derivation_statement_of_extraction_statement
            topologyStatement M extinction⟩) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload is the fixed-extinction
payload of the dependency-level theorem-shaped topology extraction statement.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_extraction_statement_payload_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      topology_extraction_statement_payload_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction derivation payload is the payload of the
dependency-level theorem-shaped topology statement.
-/
theorem topology_derivation_statement_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_dependencies
      dependencies M extinction =
      topology_derivation_statement_payload_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction homeomorphism is the homeomorphism
projection from the dependency-level theorem-shaped topology statement.
-/
theorem homeomorphism_of_extinction_and_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_extinction_and_dependencies dependencies M extinction =
      homeomorphism_of_topology_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level theorem-shaped topology statement supplies the lifted
homeomorphism derivation statement for the projected dependency-level
homeomorphism.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyLiftedHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        dependencies M extinction) := by
  rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
    dependencies M extinction]
  exact topology_lifted_homeomorphism_derivation_statement_of_extraction_statement
    (topology_extraction_statement_of_dependencies dependencies) M extinction

/--
The dependency-level lifted homeomorphism derivation statement follows the
dependency-level theorem-shaped topology statement.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact
          topology_lifted_homeomorphism_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level lifted homeomorphism derivation statement agrees with the
direct extraction-statement route.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact
          topology_lifted_homeomorphism_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level lifted homeomorphism derivation statement agrees with the
stored topology package route.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact topology_lifted_homeomorphism_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation statement selected through the
extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_derivation_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_derivation_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement selected through the
extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_homeomorphism_assembly_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_assembly_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition statement selected through
the extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_simply_connected_recognition_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_via_extraction_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient statement selected through the
extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_spherical_trivial_quotient_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_via_extraction_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift statement selected through
the extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_spherical_homeomorphism_lift_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_via_extraction_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement selected through the
extraction payload follows the dependency-level theorem-shaped topology
statement.
-/
theorem topology_homeomorphism_derivation_statement_via_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_via_extraction_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_derivation_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level topology classification sub-obligation projection is the
classification projection of the dependency-level theorem-shaped topology
statement.
-/
theorem topology_classification_subobligations_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      topology_classification_subobligations_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction)
        (topology_derivation_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition substatement is the
recognition projection of the dependency-level theorem-shaped topology
statement.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient substatement is the
trivial-quotient projection of the dependency-level theorem-shaped topology
statement.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift substatement is the lift
projection of the dependency-level theorem-shaped topology statement.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation statement follows the derivation
projection of the dependency-level theorem-shaped topology statement.
-/
theorem topology_derivation_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_dependencies dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_derivation_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement follows the derivation
statement projected from the dependency-level theorem-shaped topology statement.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_assembly_statement_of_derivation_statement
          M extinction
          (homeomorphism_of_topology_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction)
          (topology_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement follows the derivation
statement projected from the dependency-level theorem-shaped topology statement.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_derivation_statement_of_derivation_statement
          M extinction
          (homeomorphism_of_topology_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction)
          (topology_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly certificate follows the assembly
statement projected from the dependency-level theorem-shaped topology statement.
-/
theorem topology_homeomorphism_assembly_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        rcases topology_homeomorphism_assembly_statement_of_derivation_statement
            M extinction
            (homeomorphism_of_topology_extraction_statement
              (topology_extraction_statement_of_dependencies dependencies)
              M extinction)
            (topology_derivation_statement_of_extraction_statement
              (topology_extraction_statement_of_dependencies dependencies)
              M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation certificate follows the
derivation statement projected from the dependency-level theorem-shaped
topology statement.
-/
theorem topology_homeomorphism_derivation_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        rcases topology_homeomorphism_derivation_statement_of_derivation_statement
            M extinction
            (homeomorphism_of_topology_extraction_statement
              (topology_extraction_statement_of_dependencies dependencies)
              M extinction)
            (topology_derivation_statement_of_extraction_statement
              (topology_extraction_statement_of_dependencies dependencies)
              M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
The dependency-level topology classification sub-obligation projection is also
the classification projection of the stored topology package derivation route.
-/
theorem topology_classification_subobligations_of_dependencies_to_package_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      topology_classification_subobligations_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package dependencies.topology M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition substatement is also the
recognition projection of the stored topology package derivation route.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_to_package_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package dependencies.topology M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient substatement is also the
trivial-quotient projection of the stored topology package derivation route.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_to_package_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package dependencies.topology M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift substatement is also the
lift projection of the stored topology package derivation route.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_to_package_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_derivation_statement
        M extinction
        (homeomorphism_of_topology_package dependencies.topology M extinction)
        (extinction_topology_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation statement follows the derivation route
of the stored topology package.
-/
theorem topology_derivation_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_dependencies dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact extinction_topology_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement follows the stored
topology package derivation route.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact topology_homeomorphism_assembly_statement_of_derivation_statement
          M extinction
          (homeomorphism_of_topology_package dependencies.topology M extinction)
          (extinction_topology_derivation_statement_of_topology_package
            dependencies.topology M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement follows the stored
topology package derivation route.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact topology_homeomorphism_derivation_statement_of_derivation_statement
          M extinction
          (homeomorphism_of_topology_package dependencies.topology M extinction)
          (extinction_topology_derivation_statement_of_topology_package
            dependencies.topology M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly certificate follows the stored
topology package derivation route.
-/
theorem topology_homeomorphism_assembly_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        rcases topology_homeomorphism_assembly_statement_of_derivation_statement
            M extinction
            (homeomorphism_of_topology_package dependencies.topology
              M extinction)
            (extinction_topology_derivation_statement_of_topology_package
              dependencies.topology M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation certificate follows the stored
topology package derivation route.
-/
theorem topology_homeomorphism_derivation_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        rcases topology_homeomorphism_derivation_statement_of_derivation_statement
            M extinction
            (homeomorphism_of_topology_package dependencies.topology
              M extinction)
            (extinction_topology_derivation_statement_of_topology_package
              dependencies.topology M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
The dependency-level classification projection follows the direct projection
from the dependency-level theorem-shaped topology extraction statement.
-/
theorem topology_classification_subobligations_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      topology_classification_subobligations_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition substatement follows the
direct projection from the dependency-level theorem-shaped topology extraction
statement.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient substatement follows the direct
projection from the dependency-level theorem-shaped topology extraction
statement.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift substatement follows the
direct projection from the dependency-level theorem-shaped topology extraction
statement.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement follows the direct
projection from the dependency-level theorem-shaped topology extraction
statement.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_assembly_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement follows the direct
projection from the dependency-level theorem-shaped topology extraction
statement.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        exact topology_homeomorphism_derivation_statement_of_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)
          M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly certificate follows the direct
assembly statement projected from the dependency-level theorem-shaped topology
extraction statement.
-/
theorem topology_homeomorphism_assembly_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        rcases topology_homeomorphism_assembly_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation certificate follows the direct
derivation statement projected from the dependency-level theorem-shaped
topology extraction statement.
-/
theorem topology_homeomorphism_derivation_of_dependencies_to_extraction_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          dependencies M extinction]
        rcases topology_homeomorphism_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies dependencies)
            M extinction with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
The dependency-level simply-connected recognition substatement follows the
direct statement projection of the stored topology package.
-/
theorem topology_simply_connected_recognition_statement_of_dependencies_to_package_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_dependencies
      dependencies M extinction =
      topology_simply_connected_recognition_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical trivial-quotient substatement follows the direct
statement projection of the stored topology package.
-/
theorem topology_spherical_trivial_quotient_statement_of_dependencies_to_package_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level spherical homeomorphism-lift substatement follows the
direct statement projection of the stored topology package.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_dependencies_to_package_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_dependencies
      dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_topology_package
        dependencies.topology M extinction := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement follows the direct
statement projection of the stored topology package.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_package_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact topology_homeomorphism_assembly_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement follows the direct
statement projection of the stored topology package.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_package_statement_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_package_eq
          dependencies M extinction]
        exact topology_homeomorphism_derivation_statement_of_topology_package
          dependencies.topology M extinction) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the theorem-shaped smoothability bridge
used by the surgery layer.
-/
theorem smoothability_bridge_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  smoothability_bridge_of_smoothability_package
    (smoothability_package_of_dependencies dependencies)

/--
A completed dependency package supplies the smoothability bridge payload:
manifold evidence together with bridge derivation, model compatibility, and
chart compatibility, plus the full smoothability sub-obligation stack.
-/
theorem smoothability_bridge_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    ∃ manifoldEvidence : IsManifold ThreeManifoldModelWithCorners 1 M,
    ∃ bridgeDerivation :
      HasSmoothabilityBridgeDerivation M
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M)
        (smoothability_smooth_structure_derivation_statement_of_dependencies
          dependencies M)
        manifoldEvidence,
    ∃ modelCompatibility :
      HasSmoothManifoldModelCompatibility M
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M)
        (smoothability_smooth_structure_derivation_statement_of_dependencies
          dependencies M)
        manifoldEvidence
        bridgeDerivation,
    ∃ _chartCompatibility :
      HasSmoothChartCompatibility M
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M)
        (smoothability_smooth_structure_derivation_statement_of_dependencies
          dependencies M)
        manifoldEvidence
        bridgeDerivation
        modelCompatibility,
      SmoothabilitySubobligationsPayload M := by
  let package := smoothability_package_of_dependencies dependencies
  let smoothStructure :=
    smooth_structure_of_smoothability_package package M
  let smoothDerivationStatement :=
    smoothability_smooth_structure_derivation_statement_of_dependencies
      dependencies M
  rcases smoothability_bridge_payload_of_smoothability_package package M with
    ⟨manifoldEvidence, bridgeDerivation, modelCompatibility,
      chartCompatibility, subobligations⟩
  let bridgeDerivation' :
      HasSmoothabilityBridgeDerivation M
        smoothStructure smoothDerivationStatement manifoldEvidence := by
    convert bridgeDerivation
  let modelCompatibility' :
      HasSmoothManifoldModelCompatibility M
        smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation' := by
    convert modelCompatibility
  let chartCompatibility' :
      HasSmoothChartCompatibility M
        smoothStructure smoothDerivationStatement manifoldEvidence
        bridgeDerivation' modelCompatibility' := by
    convert chartCompatibility
  exact ⟨manifoldEvidence, bridgeDerivation', modelCompatibility',
    chartCompatibility', subobligations⟩

/--
A completed dependency package supplies the raw smoothability bridge used by the
surgery layer by applying the theorem-shaped bridge statement.
-/
theorem smoothability_bridge_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold ThreeManifoldModelWithCorners 1 M := by
  intro M _ _ _ _ _
  rcases smoothability_bridge_payload_of_dependencies dependencies M with
    ⟨manifoldEvidence, _bridgeDerivation, _modelCompatibility,
      _chartCompatibility, _subobligations⟩
  exact manifoldEvidence

/--
A completed dependency package supplies the theorem-shaped `C∞`
smooth-manifold statement consumed by the canonical smooth Poincare statement.
-/
theorem smoothability_smooth_manifold_statement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    SmoothabilitySmoothManifoldStatement.{u} :=
  smoothability_smooth_manifold_statement_of_smoothability_package
    (smoothability_package_of_dependencies dependencies)

/--
A completed dependency package supplies the `C∞` manifold evidence consumed by
the canonical smooth Poincare statement.
-/
theorem smooth_manifold_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        IsManifold (𝓡 3) ∞ M :=
  smoothability_smooth_manifold_statement_of_dependencies dependencies

/--
A completed dependency package exposes both smoothability theorem outputs:
the C¹ surgery-model bridge and the separate `C∞` canonical smooth-manifold
statement.
-/
theorem smoothability_smooth_manifold_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    SmoothabilityBridgeStatement.{u} ∧
      SmoothabilitySmoothManifoldStatement.{u} :=
  ⟨smoothability_bridge_statement_of_dependencies dependencies,
    smoothability_smooth_manifold_statement_of_dependencies dependencies⟩

/-- The dependency-level smoothability bridge statement is the stored field. -/
theorem smoothability_bridge_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_bridge_statement_of_dependencies dependencies =
      dependencies.smoothability.bridge :=
  rfl

/-- The dependency-level `C∞` smooth-manifold statement is the stored field. -/
theorem smoothability_smooth_manifold_statement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_smooth_manifold_statement_of_dependencies dependencies =
      dependencies.smoothability.smoothManifold :=
  rfl

/-- The dependency-level canonical smooth-manifold projection is the stored field. -/
theorem smooth_manifold_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smooth_manifold_of_dependencies dependencies =
      dependencies.smoothability.smoothManifold := by
  apply Subsingleton.elim

/-- The dependency-level smooth-manifold payload is the pair of stored fields. -/
theorem smoothability_smooth_manifold_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_smooth_manifold_payload_of_dependencies dependencies =
      ⟨dependencies.smoothability.bridge,
        dependencies.smoothability.smoothManifold⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies derivation evidence for the
smoothability bridge used by the surgery chart model through the bridge payload.
-/
theorem smoothability_bridge_derivation_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothabilityBridgeDerivation M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M)
      (smoothability_smooth_structure_derivation_statement_of_dependencies
        dependencies M)
      (smoothability_bridge_of_dependencies dependencies M) := by
  rcases smoothability_bridge_payload_of_dependencies dependencies M with
    ⟨manifoldEvidence, bridgeDerivation, _modelCompatibility,
      _chartCompatibility, _subobligations⟩
  convert bridgeDerivation

/--
A completed dependency package supplies compatibility of the produced manifold
instance with the intended smooth model through the bridge payload.
-/
theorem smoothability_model_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothManifoldModelCompatibility M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M)
      (smoothability_smooth_structure_derivation_statement_of_dependencies
        dependencies M)
      (smoothability_bridge_of_dependencies dependencies M)
      (smoothability_bridge_derivation_of_dependencies dependencies M) := by
  rcases smoothability_bridge_payload_of_dependencies dependencies M with
    ⟨manifoldEvidence, bridgeDerivation, modelCompatibility,
      _chartCompatibility, _subobligations⟩
  convert modelCompatibility

/--
A completed dependency package supplies compatibility between its smooth
structure and the surgery chart model through the bridge payload.
-/
theorem smoothability_chart_compatibility_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    HasSmoothChartCompatibility M
      (smooth_structure_of_smoothability_package
        (smoothability_package_of_dependencies dependencies) M)
      (smoothability_smooth_structure_derivation_statement_of_dependencies
        dependencies M)
      (smoothability_bridge_of_dependencies dependencies M)
      (smoothability_bridge_derivation_of_dependencies dependencies M)
      (smoothability_model_compatibility_of_dependencies dependencies M) := by
  rcases smoothability_bridge_payload_of_dependencies dependencies M with
    ⟨manifoldEvidence, bridgeDerivation, modelCompatibility,
      chartCompatibility, _subobligations⟩
  convert chartCompatibility

/--
A completed dependency package supplies the named full smoothability
sub-obligation payload through the smoothability bridge payload.
-/
theorem smoothability_subobligations_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    SmoothabilitySubobligationsPayload M := by
  rcases smoothability_bridge_payload_of_dependencies dependencies M with
    ⟨_manifoldEvidence, _bridgeDerivation, _modelCompatibility,
      _chartCompatibility, subobligations⟩
  exact subobligations

/--
The dependency-level raw bridge is the raw bridge projection of the stored
smoothability package.
-/
theorem smoothability_bridge_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    smoothability_bridge_of_dependencies dependencies =
      smoothable_of_smoothability_package dependencies.smoothability := by
  apply Subsingleton.elim

/--
The dependency-level bridge derivation is the corresponding bridge-derivation
projection of the stored smoothability package.
-/
theorem smoothability_bridge_derivation_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_derivation_of_dependencies dependencies M =
      smoothability_bridge_derivation_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
The dependency-level smooth-model compatibility proof is the corresponding
compatibility projection of the stored smoothability package.
-/
theorem smoothability_model_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_model_compatibility_of_dependencies dependencies M =
      smooth_model_compatibility_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
The dependency-level smooth-chart compatibility proof is the corresponding
chart-compatibility projection of the stored smoothability package.
-/
theorem smoothability_chart_compatibility_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_chart_compatibility_of_dependencies dependencies M =
      smooth_chart_compatibility_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
The dependency-level bridge payload is the tuple of named dependency-level
bridge projections.
-/
theorem smoothability_bridge_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_bridge_payload_of_dependencies dependencies M =
      ⟨smoothability_bridge_of_dependencies dependencies M,
        smoothability_bridge_derivation_of_dependencies dependencies M,
        smoothability_model_compatibility_of_dependencies dependencies M,
        smoothability_chart_compatibility_of_dependencies dependencies M,
        smoothability_subobligations_payload_of_dependencies
          dependencies M⟩ := by
  apply Subsingleton.elim

/--
The dependency-level smoothability sub-obligation payload is the reconstructed
payload determined by the named bridge derivation and compatibility proofs.
-/
theorem smoothability_subobligations_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_payload_of_dependencies dependencies M =
      smoothability_subobligations_of_derivation_statement M
        (smooth_structure_of_smoothability_package
          (smoothability_package_of_dependencies dependencies) M)
        (smoothability_smooth_structure_derivation_statement_of_dependencies
          dependencies M)
        (smoothability_bridge_of_dependencies dependencies M)
        (smoothability_bridge_derivation_of_dependencies dependencies M)
        (smoothability_model_compatibility_of_dependencies dependencies M)
        (smoothability_chart_compatibility_of_dependencies dependencies M) := by
  apply Subsingleton.elim

/--
The dependency-level smoothability sub-obligation payload agrees with the direct
smoothability-package sub-obligation bridge.
-/
theorem smoothability_subobligations_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_payload_of_dependencies dependencies M =
      smoothability_subobligations_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the full smoothability bridge
sub-obligation stack for any target topological 3-manifold.
-/
theorem smoothability_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
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
  exact smoothability_subobligations_payload_of_dependencies dependencies M

/--
The dependency-level smoothability sub-obligation stack is the named bridge
payload projection.
-/
theorem smoothability_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_dependencies dependencies M =
      smoothability_subobligations_payload_of_dependencies dependencies M := by
  apply Subsingleton.elim

/--
The dependency-level smoothability sub-obligation stack agrees with the direct
smoothability-package sub-obligation bridge.
-/
theorem smoothability_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    smoothability_subobligations_of_dependencies dependencies M =
      smoothability_subobligations_of_smoothability_package
        dependencies.smoothability M := by
  apply Subsingleton.elim

/--
A completed dependency package supplies statement-mediated finite-extinction
packages for every target manifold once the smoothability bridge has produced
the required smooth manifold instance.
-/
theorem finite_extinction_statements_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω, FiniteExtinctionStatement n M := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _flow, _surgery, _control, packageStatement,
      _subobligationsStatement, _viaSubobligationsStatement,
      _derivation, _finiteExtinction⟩
  exact ⟨n, packageStatement⟩

/--
The dependency-level finite-extinction package-statement projection is selected
from the named finite-extinction statement payload.
-/
theorem finite_extinction_statements_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_of_dependencies dependencies M
    finite_extinction_statements_of_dependencies dependencies M =
      ⟨payload.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction package-statement projection follows the
direct finite-extinction statement of the selected surgery package.
-/
theorem finite_extinction_statements_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_statements_of_dependencies dependencies M =
      ⟨payload.choose,
        finite_extinction_statement_of_surgery_package
          payload.choose_spec.choose⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies theorem-shaped finite-extinction
statements through the full sub-obligation statement route.
-/
theorem finite_extinction_statements_via_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M]
      [IsManifold ThreeManifoldModelWithCorners 1 M],
        ∃ n : ℕ∞ω, FiniteExtinctionStatement n M := by
  intro M _ _ _ _ _ _
  rcases finite_extinction_statement_payload_of_dependencies
      dependencies M with
    ⟨n, _flow, _surgery, _control, _packageStatement,
      _subobligationsStatement, viaSubobligationsStatement,
      _derivation, _finiteExtinction⟩
  exact ⟨n, viaSubobligationsStatement⟩

/--
The dependency-level finite-extinction via-subobligations statement projection
is selected from the named finite-extinction statement payload.
-/
theorem finite_extinction_statements_via_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_of_dependencies dependencies M
    finite_extinction_statements_via_subobligations_of_dependencies dependencies M =
      ⟨payload.choose,
        payload.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩ := by
  dsimp

/--
The dependency-level finite-extinction via-subobligations statement projection
follows the sub-obligation statement of the selected surgery package.
-/
theorem finite_extinction_statements_via_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    let payload :=
      finite_extinction_statement_payload_with_surgery_package_of_dependencies
        dependencies M
    finite_extinction_statements_via_subobligations_of_dependencies
        dependencies M =
      ⟨payload.choose,
        finite_extinction_statement_of_subobligations_statement
          (finite_extinction_subobligations_statement_of_surgery_package
            payload.choose_spec.choose)⟩ := by
  apply Subsingleton.elim

/--
A completed dependency package supplies finite extinction directly through the
statement-mediated full finite-extinction sub-obligation route.
-/
theorem finite_extinction_via_subobligations_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _
  letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
    smoothability_bridge_of_dependencies dependencies M
  rcases finite_extinction_statement_payload_of_dependencies
      dependencies M with
    ⟨_n, _flow, _surgery, _control, _packageStatement,
      _subobligationsStatement, _viaSubobligationsStatement,
      _derivation, finiteExtinction⟩
  exact finiteExtinction

/--
The dependency-level finite-extinction theorem is selected from the named
finite-extinction statement payload after installing the smoothability bridge.
-/
theorem finite_extinction_via_subobligations_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_via_subobligations_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies dependencies M
        rcases finite_extinction_statement_payload_of_dependencies
            dependencies M with
          ⟨_n, _flow, _surgery, _control, _packageStatement,
            _subobligationsStatement, _viaSubobligationsStatement,
            _derivation, finiteExtinction⟩
        exact finiteExtinction) := by
  apply Subsingleton.elim

/--
The dependency-level finite-extinction theorem follows the extinction witness
extracted from the selected surgery package's full sub-obligation statement.
-/
theorem finite_extinction_via_subobligations_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_via_subobligations_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies dependencies M
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨_n, surgeryPackage, _analyticPackage, _analyticPackage_eq,
            _flow, _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        exact
          finite_extinction_of_subobligations_statement
            (finite_extinction_subobligations_statement_of_surgery_package
              surgeryPackage)) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the finite-extinction conclusion for
every target manifold.
-/
theorem finite_extinction_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _
  exact finite_extinction_via_subobligations_of_dependencies dependencies M

/--
The dependency-level finite-extinction theorem is the named
subobligations-route finite-extinction theorem.
-/
theorem finite_extinction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_of_dependencies dependencies =
      finite_extinction_via_subobligations_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The dependency-level finite-extinction theorem agrees directly with the
extinction witness extracted from the selected surgery package's full
sub-obligation statement.
-/
theorem finite_extinction_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    finite_extinction_of_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies dependencies M
        rcases surgery_package_payload_of_dependencies dependencies M with
          ⟨_n, surgeryPackage, _analyticPackage, _analyticPackage_eq,
            _flow, _flow_eq, _constructionPackage, _constructionPackage_heq,
            _controlPackage, _controlPackage_heq⟩
        exact
          finite_extinction_of_subobligations_statement
            (finite_extinction_subobligations_statement_of_surgery_package
              surgeryPackage)) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the named universal finite-extinction
boundary used by the finite-extinction-only completion route.
-/
theorem universalFiniteExtinctionStatement_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  finite_extinction_via_subobligations_of_dependencies dependencies

/--
The dependency-level universal finite-extinction boundary is exactly the
named subobligations-route finite-extinction projection.
-/
theorem universalFiniteExtinctionStatement_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    universalFiniteExtinctionStatement_of_dependencies dependencies =
      finite_extinction_via_subobligations_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The dependency-level universal finite-extinction boundary follows the shared
finite-extinction package route instead of reopening the surgery package
payload.
-/
theorem universalFiniteExtinctionStatement_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    universalFiniteExtinctionStatement_of_dependencies dependencies =
      finite_extinction_via_subobligations_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies finite extinction by installing
its smoothability bridge and extracting the witness from the named
equation-boundary verification payload.
-/
theorem finite_extinction_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M := by
  intro M _ _ _ _ _
  letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
    smoothability_bridge_of_dependencies
      (dependencies_of_equation_boundary_dependencies dependencies) M
  exact
    finite_extinction_of_equation_boundary_verification_payload
      (equation_boundary_verification_payload_of_dependencies dependencies) M

/--
The strengthened dependency finite-extinction theorem is exactly the
verification-payload route after installing the forgetful smoothability bridge.
-/
theorem finite_extinction_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finite_extinction_of_equation_boundary_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies) M
        exact
          finite_extinction_of_equation_boundary_verification_payload
            (equation_boundary_verification_payload_of_dependencies
              dependencies) M) := by
  apply Subsingleton.elim

/--
The strengthened dependency finite-extinction theorem is the finite-extinction
projection of the named verification payload.
-/
theorem finite_extinction_of_equation_boundary_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finite_extinction_of_equation_boundary_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies) M
        exact
          finite_extinction_of_equation_boundary_verification_payload
            (equation_boundary_verification_payload_of_dependencies
              dependencies) M) := by
  apply Subsingleton.elim

/--
The strengthened dependency finite-extinction theorem is the finite-extinction
projection of the scalar-pointwise surgery payload reconstructed from the named
verification payload.
-/
theorem finite_extinction_of_equation_boundary_dependencies_to_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finite_extinction_of_equation_boundary_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies) M
        rcases
            surgery_package_with_equation_boundary_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨_n, _package, pointwisePayload⟩
        exact finite_extinction_of_pointwise_equation_payload
          pointwisePayload) := by
  apply Subsingleton.elim

/--
The strengthened dependency finite-extinction theorem is reconstructed from the
strengthened dependency direct stored-verification scalar equation payload.
-/
theorem finite_extinction_of_equation_boundary_dependencies_to_direct_pointwise_equation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finite_extinction_of_equation_boundary_dependencies dependencies =
      (by
        intro M _ _ _ _ _
        letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
          smoothability_bridge_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies) M
        rcases
            equation_boundary_direct_pointwise_equation_payload_of_dependencies
              dependencies M with
          ⟨_n, _package, directPayload⟩
        exact finite_extinction_of_direct_pointwise_equation_payload
          directPayload) := by
  apply Subsingleton.elim

/--
Forgetting equation boundaries and then using the ordinary dependency
finite-extinction theorem agrees with the strengthened dependency
finite-extinction route.
-/
theorem finite_extinction_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    finite_extinction_of_equation_boundary_dependencies dependencies =
      finite_extinction_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
A strengthened dependency package supplies the named universal finite-extinction
boundary used by the finite-extinction-only completion route.
-/
theorem universalFiniteExtinctionStatement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  finite_extinction_of_equation_boundary_dependencies dependencies

/--
The strengthened dependency universal finite-extinction boundary is exactly the
strengthened finite-extinction projection.
-/
theorem universalFiniteExtinctionStatement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    universalFiniteExtinctionStatement_of_equation_boundary_dependencies
        dependencies =
      finite_extinction_of_equation_boundary_dependencies dependencies := by
  apply Subsingleton.elim

/--
The strengthened dependency universal finite-extinction boundary agrees with
the ordinary dependency universal boundary after forgetting equation data.
-/
theorem universalFiniteExtinctionStatement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    universalFiniteExtinctionStatement_of_equation_boundary_dependencies
        dependencies =
      universalFiniteExtinctionStatement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the post-extinction topological
extraction theorem used by the final assembly layer.
-/
theorem extinction_extraction_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  rcases topology_extraction_payload_of_dependencies dependencies with
    ⟨_topologyStatement, extraction⟩
  exact extraction

/--
The dependency-level final extractor is the final extractor supplied by the
stored topology package.
-/
theorem extinction_extraction_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinction_extraction_of_dependencies dependencies =
      extinction_implies_sphere_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level final extractor follows the stored topology package route.
-/
theorem extinction_extraction_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinction_extraction_of_dependencies dependencies =
      extinction_implies_sphere_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
A completed dependency package supplies a final extractor paired with the
post-extinction topology derivation certificate for that extractor.
-/
theorem topology_extraction_derivation_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  exact topology_extraction_derivation_payload_of_topology_package
    (topology_package_of_dependencies dependencies)

/--
The dependency-level extraction/derivation payload is the corresponding payload
of the stored topology package.
-/
theorem topology_extraction_derivation_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_derivation_payload_of_dependencies dependencies =
      topology_extraction_derivation_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level extraction/derivation payload follows the stored topology
package route.
-/
theorem topology_extraction_derivation_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_derivation_payload_of_dependencies dependencies =
      topology_extraction_derivation_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level final extractor agrees with the extractor mediated by the
dependency-level theorem-shaped topology statement.
-/
theorem extinction_extraction_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinction_extraction_of_dependencies dependencies =
      extinction_implies_sphere_of_topology_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The dependency-level extraction/derivation payload is the forward direction of
the extraction/derivation equivalence for the dependency-level topology
statement.
-/
theorem topology_extraction_derivation_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_derivation_payload_of_dependencies dependencies =
      extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
        (topology_extraction_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies a final extractor, its full topology
derivation certificate, and the lifted homeomorphism derivation certificate
for the extractor's chosen homeomorphism.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} :=
  topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
    (topology_package_of_dependencies dependencies)

/--
The dependency-level lifted-homeomorphism extraction payload is the
corresponding payload of the stored topology package.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level lifted-homeomorphism extraction payload follows the stored
topology package route.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
        dependencies.topology := by
  apply Subsingleton.elim

/--
The dependency-level lifted-homeomorphism extraction payload is the forward
direction of the lifted extraction/derivation equivalence for the
dependency-level topology statement.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
        (topology_extraction_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The dependency-level lifted-homeomorphism extraction payload is obtained from
the ordinary dependency extraction/derivation payload by attaching the lifted
derivation projection.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_to_derivation_payload_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨extractSphere, derivation,
          topology_lifted_homeomorphism_derivation_for_extraction_statement_of_derivation_for_extraction_statement
            extractSphere derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the post-extinction topological
extraction theorem after forgetting equation-boundary data.
-/
theorem extinction_extraction_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ExtinctionImpliesSphereStatement.{u} :=
  extinction_extraction_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened dependency final extractor is the ordinary dependency final
extractor of the forgetful package.
-/
theorem extinction_extraction_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    extinction_extraction_of_equation_boundary_dependencies dependencies =
      extinction_extraction_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency final extractor agrees directly with the forgetful
ordinary dependency final extractor.
-/
theorem extinction_extraction_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    extinction_extraction_of_equation_boundary_dependencies dependencies =
      extinction_extraction_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency final extractor is the extractor mediated by the
forgetful theorem-shaped topology statement.
-/
theorem extinction_extraction_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    extinction_extraction_of_equation_boundary_dependencies dependencies =
      extinction_implies_sphere_of_topology_extraction_statement
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies)) := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies a final extractor paired with its
topology derivation certificate after forgetting equation-boundary data.
-/
theorem topology_extraction_derivation_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere :=
  topology_extraction_derivation_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened dependency extraction/derivation payload is the ordinary
dependency extraction/derivation payload of the forgetful package.
-/
theorem topology_extraction_derivation_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      topology_extraction_derivation_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency extraction/derivation payload agrees directly with
the forgetful ordinary dependency extraction/derivation payload.
-/
theorem topology_extraction_derivation_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      topology_extraction_derivation_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the lifted-homeomorphism
extraction payload after forgetting equation-boundary data.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ExtinctionTopologyExtractionWithLiftedHomeomorphismDerivationStatement.{u} :=
  topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies)

/--
The strengthened lifted-homeomorphism extraction payload is the ordinary
dependency lifted-homeomorphism extraction payload of the forgetful package.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism extraction payload agrees directly with
the forgetful ordinary dependency route.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism extraction payload is the forward
direction of the lifted extraction/derivation equivalence for the forgetful
theorem-shaped topology statement.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies)) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism extraction payload is obtained from the
ordinary strengthened extraction/derivation payload by attaching the lifted
derivation projection.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies_to_derivation_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨extractSphere, derivation,
          topology_lifted_homeomorphism_derivation_for_extraction_statement_of_derivation_for_extraction_statement
            extractSphere derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the simply-connected recognition
substatement after forgetting equation-boundary data.
-/
theorem topology_simply_connected_recognition_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySimplyConnectedRecognitionStatement M extinction :=
  topology_simply_connected_recognition_statement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) M extinction

/--
The strengthened simply-connected recognition statement is the ordinary
dependency recognition statement of the forgetful package.
-/
theorem topology_simply_connected_recognition_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_simply_connected_recognition_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened simply-connected recognition statement agrees directly with
the forgetful ordinary dependency route.
-/
theorem topology_simply_connected_recognition_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_simply_connected_recognition_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened simply-connected recognition statement is projected from the
forgetful theorem-shaped topology extraction statement.
-/
theorem topology_simply_connected_recognition_statement_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_simply_connected_recognition_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_simply_connected_recognition_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies))
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the spherical trivial-quotient
substatement after forgetting equation-boundary data.
-/
theorem topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalTrivialQuotientStatement M extinction :=
  topology_spherical_trivial_quotient_statement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) M extinction

/--
The strengthened spherical trivial-quotient statement is the ordinary
dependency trivial-quotient statement of the forgetful package.
-/
theorem topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened spherical trivial-quotient statement agrees directly with the
forgetful ordinary dependency route.
-/
theorem topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened spherical trivial-quotient statement is projected from the
forgetful theorem-shaped topology extraction statement.
-/
theorem topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_trivial_quotient_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_trivial_quotient_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies))
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the spherical homeomorphism-lift
substatement after forgetting equation-boundary data.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologySphericalHomeomorphismLiftStatement M extinction :=
  topology_spherical_homeomorphism_lift_statement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) M extinction

/--
The strengthened spherical homeomorphism-lift statement is the ordinary
dependency lift statement of the forgetful package.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened spherical homeomorphism-lift statement agrees directly with
the forgetful ordinary dependency route.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened spherical homeomorphism-lift statement is projected from the
forgetful theorem-shaped topology extraction statement.
-/
theorem topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_spherical_homeomorphism_lift_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_spherical_homeomorphism_lift_statement_of_extraction_statement
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies))
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened dependency package supplies the lifted homeomorphism
derivation statement after forgetting equation-boundary data.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    ExtinctionTopologyLiftedHomeomorphismDerivationStatement M extinction
      (homeomorphism_of_extinction_and_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction) :=
  topology_lifted_homeomorphism_derivation_statement_of_dependencies
    (dependencies_of_equation_boundary_dependencies dependencies) M extinction

/--
The strengthened lifted homeomorphism derivation statement is the ordinary
dependency lifted derivation statement of the forgetful package.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_lifted_homeomorphism_derivation_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened lifted homeomorphism derivation statement agrees directly
with the forgetful ordinary dependency route.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      topology_lifted_homeomorphism_derivation_statement_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The strengthened lifted homeomorphism derivation statement is projected from
the forgetful theorem-shaped topology extraction statement.
-/
theorem topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_lifted_homeomorphism_derivation_statement_of_equation_boundary_dependencies
        dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_statement_eq
          (dependencies_of_equation_boundary_dependencies dependencies)
          M extinction]
        exact
          topology_lifted_homeomorphism_derivation_statement_of_extraction_statement
            (topology_extraction_statement_of_dependencies
              (dependencies_of_equation_boundary_dependencies dependencies))
            M extinction) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the two theorem-shaped inputs consumed
by the final finite-extinction/topology-extraction assembly theorem through the
projection route.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} := by
  let finiteExtinction := finite_extinction_of_dependencies dependencies
  let extraction := extinction_extraction_of_dependencies dependencies
  exact ⟨finiteExtinction, extraction⟩

/--
The projection assembly-input payload is the pair of named finite-extinction
and post-extinction extraction projections.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_dependencies dependencies =
      ⟨finite_extinction_of_dependencies dependencies,
        extinction_extraction_of_dependencies dependencies⟩ := by
  apply Subsingleton.elim

/--
The dependency projection assembly-input payload is the dependency-level finite
extinction route paired with the extractor mediated by the dependency-level
theorem-shaped topology statement.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_dependencies dependencies =
      ⟨finite_extinction_of_dependencies dependencies,
        extinction_implies_sphere_of_topology_extraction_statement
          (topology_extraction_statement_of_dependencies dependencies)⟩ := by
  apply Subsingleton.elim

/--
The dependency projection assembly-input payload is the dependency-level finite
extinction route paired with the final extractor selected by the stored
topology package.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_dependencies dependencies =
      ⟨finite_extinction_of_dependencies dependencies,
        extinction_implies_sphere_of_topology_package
          dependencies.topology⟩ := by
  apply Subsingleton.elim

/--
A strengthened dependency package supplies the finite-extinction input through
its boundary route and the topology-extraction input through the forgetful
topology package.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} :=
  ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
    extinction_extraction_of_equation_boundary_dependencies dependencies⟩

/--
The strengthened dependency projection assembly-input payload is the pair of
the strengthened finite-extinction route and the forgetful final extractor.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
        extinction_extraction_of_equation_boundary_dependencies dependencies⟩ := by
  apply Subsingleton.elim

/--
The strengthened dependency projection assembly-input payload pairs
verification-payload finite extinction with the forgetful final extractor.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies_to_verification_payload_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_extraction_of_equation_boundary_dependencies dependencies
        exact ⟨finiteExtinction, extraction⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection assembly-input payload uses the
forgetful theorem-shaped topology statement for its final extractor.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        dependencies =
      ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
        extinction_implies_sphere_of_topology_extraction_statement
          (topology_extraction_statement_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies))⟩ := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened projection assembly-input
payload recovers the ordinary dependency projection assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        dependencies =
      poincare_projection_assembly_inputs_payload_of_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionAssemblyInputs

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications supply
finite extinction through the strengthened dependency lift.
-/
theorem finite_extinction_of_dependencies_and_verification_family :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        FiniteExtinctionByRicciFlowWithSurgery M :=
  finite_extinction_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family finite-extinction route delegates to the strengthened
dependency finite-extinction route after applying the verification-family lift.
-/
theorem finite_extinction_of_dependencies_and_verification_family_eq :
    finite_extinction_of_dependencies_and_verification_family
        dependencies verificationFamily =
      finite_extinction_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
finite-extinction route.
-/
theorem finite_extinction_of_dependencies_and_verification_family_to_dependencies_eq :
    finite_extinction_of_dependencies_and_verification_family
        dependencies verificationFamily =
      finite_extinction_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
Ordinary aggregate dependencies plus explicit equation verifications supply the
post-extinction topology extractor through the strengthened dependency lift.
-/
theorem extinction_extraction_of_dependencies_and_verification_family :
    ExtinctionImpliesSphereStatement.{u} :=
  extinction_extraction_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family topology-extraction route delegates to the strengthened
dependency topology-extraction route after applying the verification-family
lift.
-/
theorem extinction_extraction_of_dependencies_and_verification_family_eq :
    extinction_extraction_of_dependencies_and_verification_family
        dependencies verificationFamily =
      extinction_extraction_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
topology-extraction route.
-/
theorem extinction_extraction_of_dependencies_and_verification_family_to_dependencies_eq :
    extinction_extraction_of_dependencies_and_verification_family
        dependencies verificationFamily =
      extinction_extraction_of_dependencies dependencies := by
  apply Subsingleton.elim

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
two theorem-shaped inputs consumed by the projection assembly route.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} :=
  poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
    (equation_boundary_dependencies_of_dependencies_and_verification_family
      dependencies verificationFamily)

/--
The verification-family projection assembly-input payload delegates to the
strengthened dependency payload after applying the verification-family lift.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family_eq :
    poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        (equation_boundary_dependencies_of_dependencies_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
The verification-family projection assembly-input payload is the pair of the
verification-family finite-extinction route and topology extractor.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family_to_projections_eq :
    poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      ⟨finite_extinction_of_dependencies_and_verification_family
          dependencies verificationFamily,
        extinction_extraction_of_dependencies_and_verification_family
          dependencies verificationFamily⟩ := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family_to_dependencies_eq :
    poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family
        dependencies verificationFamily =
      poincare_projection_assembly_inputs_payload_of_dependencies
        dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionAssemblyInputs

/--
The projection route also exposes the finite-extinction input together with a
certified final extractor and its topology derivation certificate.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases topology_extraction_derivation_payload_of_dependencies
      dependencies with
    ⟨extractSphere, derivation⟩
  exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
    derivation⟩

/--
The certified projection assembly-input payload is selected from the named
topology extraction/derivation payload and paired with finite extinction.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection assembly-input payload is selected from
the extractor/derivation decomposition of the dependency-level topology
statement.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection assembly-input payload is selected from
the extraction/derivation payload of the stored topology package.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation⟩) := by
  apply Subsingleton.elim

/--
The dependency-level final extractor is the extractor component carried by the
ordinary finite-extinction projection assembly-input payload.
-/
theorem extinction_extraction_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinction_extraction_of_dependencies dependencies =
      (by
        rcases poincare_projection_assembly_inputs_payload_of_dependencies
            dependencies with
          ⟨_finiteExtinction, extractSphere⟩
        exact extractSphere) := by
  apply Subsingleton.elim

/--
The dependency-level final extractor is also the extractor component carried
by the certified extraction/derivation projection assembly-input payload.
-/
theorem extinction_extraction_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    extinction_extraction_of_dependencies dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
              dependencies with
          ⟨_finiteExtinction, extractSphere, _derivation⟩
        exact extractSphere) := by
  apply Subsingleton.elim

/--
The dependency-level extraction/derivation payload is recovered from the
certified projection assembly-input payload after forgetting finite
extinction.
-/
theorem topology_extraction_derivation_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_derivation_payload_of_dependencies dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
              dependencies with
          ⟨_finiteExtinction, extractSphere, derivation⟩
        exact ⟨extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
The dependency-level extraction/derivation payload is the certified payload
component of the dependency-level projection assembly inputs.
-/
theorem topology_extraction_derivation_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_derivation_payload_of_dependencies dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
              dependencies with
          ⟨_finiteExtinction, extractSphere, derivation⟩
        exact ⟨extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
The ordinary dependency projection assembly-input payload follows the explicit
finite-extinction route.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_dependencies dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        let extraction := extinction_extraction_of_dependencies dependencies
        exact ⟨finiteExtinction, extraction⟩) := by
  apply Subsingleton.elim

/--
The ordinary dependency projection assembly-input payload is the certified
projection assembly-input payload with the derivation certificate forgotten.
-/
theorem poincare_projection_assembly_inputs_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_dependencies dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
              dependencies with
          ⟨finiteExtinction, extractSphere, _derivation⟩
        exact ⟨finiteExtinction, extractSphere⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection assembly-input payload follows the
explicit finite-extinction route together with the named
extraction/derivation payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection assembly-input payload is the named
finite-extinction input paired with the dependency-level
extraction/derivation payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation⟩) := by
  apply Subsingleton.elim

/--
The dependency-level topology extraction payload can be rebuilt from the
finite-extinction assembly inputs and the dependency-level topology statement.
-/
theorem topology_extraction_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_payload_of_dependencies dependencies =
      (by
        rcases poincare_projection_assembly_inputs_payload_of_dependencies
            dependencies with
          ⟨_finiteExtinction, extractSphere⟩
        exact ⟨topology_extraction_statement_of_dependencies dependencies,
          extractSphere⟩) := by
  apply Subsingleton.elim

/--
The dependency-level topology extraction payload can be rebuilt from the
certified extraction/derivation payload after forgetting derivation evidence.
-/
theorem topology_extraction_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_payload_of_dependencies dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, _derivation⟩
        exact ⟨topology_extraction_statement_of_dependencies dependencies,
          extractSphere⟩) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload follows the explicit
finite-extinction input together with the dependency-level topology statement.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      topology_extraction_statement_payload_of_extraction_statement
        (topology_extraction_statement_of_dependencies dependencies)
        M extinction := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction topology payload can be rebuilt from the
dependency-level certified extractor and its derivation statement.
-/
theorem topology_extraction_statement_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_extraction_statement_payload_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          topology_extraction_statement_payload_of_extraction_statement
            (extinction_topology_extraction_statement_of_extraction_and_derivation
              extractSphere derivation)
            M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction derivation payload is the derivation
payload component of the fixed-extinction topology payload.
-/
theorem topology_derivation_statement_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, homeomorphism, derivationStatement,
            _classificationSubobligations, _simplyConnectedRecognition,
            _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
            _assemblyStatement, _homeomorphismDerivationStatement⟩
        exact ⟨homeomorphism, derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction derivation payload is carried by the
dependency-level certified extractor and its derivation statement.
-/
theorem topology_derivation_statement_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_payload_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨extractSphere M extinction, derivation M extinction⟩) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction homeomorphism is the homeomorphism
component of the fixed-extinction derivation payload.
-/
theorem homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_extinction_and_dependencies dependencies M extinction =
      (by
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨homeomorphism, _derivationStatement⟩
        exact homeomorphism) := by
  apply Subsingleton.elim

/--
The dependency-level fixed-extinction homeomorphism is the homeomorphism
selected by the certified dependency-level extractor.
-/
theorem homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    homeomorphism_of_extinction_and_dependencies dependencies M extinction =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, _derivation⟩
        exact extractSphere M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level classification sub-obligation projection is the
classification component of the fixed-extinction topology payload.
-/
theorem topology_classification_subobligations_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_topologyStatement, _homeomorphism, _derivationStatement,
            classificationSubobligations, _simplyConnectedRecognition,
            _sphericalTrivialQuotient, _sphericalHomeomorphismLift,
            _assemblyStatement, _homeomorphismDerivationStatement⟩
        exact classificationSubobligations) := by
  apply Subsingleton.elim

/--
The dependency-level classification sub-obligation projection is carried by
the certified dependency-level extractor and derivation statement.
-/
theorem topology_classification_subobligations_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_classification_subobligations_of_dependencies
      dependencies M extinction =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact topology_classification_subobligations_of_derivation_statement
          M extinction (extractSphere M extinction)
          (derivation M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation statement is the derivation component
of the fixed-extinction derivation payload.
-/
theorem topology_derivation_statement_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_dependencies dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨_homeomorphism, derivationStatement⟩
        exact derivationStatement) := by
  apply Subsingleton.elim

/--
The dependency-level topology derivation statement is carried by the certified
dependency-level extractor and derivation statement.
-/
theorem topology_derivation_statement_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_derivation_statement_of_dependencies dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨_extractSphere, derivation⟩
        exact derivation M extinction) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement is rebuilt from the
finite-extinction derivation payload.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨homeomorphism, derivationStatement⟩
        exact topology_homeomorphism_assembly_statement_of_derivation_statement
          M extinction homeomorphism derivationStatement) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly statement is carried by the
certified dependency-level extractor and derivation statement.
-/
theorem topology_homeomorphism_assembly_statement_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact topology_homeomorphism_assembly_statement_of_derivation_statement
          M extinction (extractSphere M extinction)
          (derivation M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement is rebuilt from the
finite-extinction derivation payload.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨homeomorphism, derivationStatement⟩
        exact topology_homeomorphism_derivation_statement_of_derivation_statement
          M extinction homeomorphism derivationStatement) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation statement is carried by the
certified dependency-level extractor and derivation statement.
-/
theorem topology_homeomorphism_derivation_statement_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_statement_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact topology_homeomorphism_derivation_statement_of_derivation_statement
          M extinction (extractSphere M extinction)
          (derivation M extinction)) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly certificate is rebuilt from the
finite-extinction derivation payload.
-/
theorem topology_homeomorphism_assembly_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨homeomorphism, derivationStatement⟩
        rcases topology_homeomorphism_assembly_statement_of_derivation_statement
            M extinction homeomorphism derivationStatement with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism assembly certificate is carried by the
certified dependency-level extractor and derivation statement.
-/
theorem topology_homeomorphism_assembly_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_assembly_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases topology_homeomorphism_assembly_statement_of_derivation_statement
            M extinction (extractSphere M extinction)
            (derivation M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction, quotientModel,
            fundamentalGroupComputation, deckGroupIdentification,
            deckGroupTriviality, simplyConnectedRecognition, trivialQuotient,
            homeomorphismAssembly⟩
        convert homeomorphismAssembly) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation certificate is rebuilt from the
finite-extinction derivation payload.
-/
theorem topology_homeomorphism_derivation_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rw [topology_homeomorphism_assembly_of_dependencies_to_finite_extinction_eq
          dependencies M extinction]
        rcases topology_derivation_statement_payload_of_dependencies
            dependencies M extinction with
          ⟨homeomorphism, derivationStatement⟩
        rcases topology_homeomorphism_derivation_statement_of_derivation_statement
            M extinction homeomorphism derivationStatement with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
The dependency-level homeomorphism derivation certificate is carried by the
certified dependency-level extractor and derivation statement.
-/
theorem topology_homeomorphism_derivation_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    topology_homeomorphism_derivation_of_dependencies
      dependencies M extinction =
      (by
        rw [homeomorphism_of_extinction_and_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rw [topology_homeomorphism_assembly_of_dependencies_to_extraction_derivation_eq
          dependencies M extinction]
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases topology_homeomorphism_derivation_statement_of_derivation_statement
            M extinction (extractSphere M extinction)
            (derivation M extinction) with
          ⟨decomposition, primeDecomposition, irreducibility,
            connectedSumCollapse, sphericalReduction,
            fundamentalGroupComputation, deckGroupTriviality,
            simplyConnectedRecognition, quotientModel, deckGroupIdentification,
            trivialQuotient, homeomorphismAssembly,
            homeomorphismDerivation⟩
        convert homeomorphismDerivation) := by
  apply Subsingleton.elim

/--
The projection route also exposes finite extinction together with the final
extractor, its full topology derivation certificate, and the lifted
homeomorphism derivation certificate.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
      ExtinctionTopologyLiftedHomeomorphismDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases
      topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies with
    ⟨extractSphere, derivation, liftedDerivation⟩
  exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
    derivation, liftedDerivation⟩

/--
The lifted-homeomorphism projection assembly-input payload is selected from
the named lifted extraction payload and paired with finite extinction.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
      dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection assembly-input payload is
selected from the lifted extraction/derivation decomposition of the
dependency-level topology statement.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection assembly-input payload also
factors through the explicit finite-extinction input and named lifted
extraction payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
      dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection assembly-input payload is
selected from the lifted extraction/derivation payload of the stored topology
package.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
      dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
              dependencies.topology with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact ⟨finite_extinction_of_dependencies dependencies, extractSphere,
          derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism projection
assembly-input payload recovers the ordinary certified extraction-derivation
assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    (by
      rcases
          poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
            dependencies with
        ⟨finiteExtinction, extractSphere, derivation,
          _liftedDerivation⟩
      exact ⟨finiteExtinction, extractSphere, derivation⟩) =
      poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
        dependencies := by
  apply Subsingleton.elim

/--
The dependency-level lifted extraction/derivation payload is recovered from
the lifted projection assembly-input payload after forgetting finite
extinction.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
              dependencies with
          ⟨_finiteExtinction, extractSphere, derivation,
            liftedDerivation⟩
        exact ⟨extractSphere, derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
The dependency-level lifted extraction/derivation payload is the ordinary
certified extraction/derivation payload with the canonical lifted derivation
attached.
-/
theorem topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact ⟨extractSphere, derivation,
          topology_lifted_homeomorphism_derivation_for_extraction_statement_of_derivation_for_extraction_statement
            extractSphere derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened projection route also exposes the boundary finite-extinction
input together with a certified final extractor and its derivation certificate.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases
      topology_extraction_derivation_payload_of_equation_boundary_dependencies
        dependencies with
    ⟨extractSphere, derivation⟩
  exact
    ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
      extractSphere, derivation⟩

/--
The strengthened certified projection assembly-input payload is selected from
the strengthened extraction/derivation payload and paired with boundary finite
extinction.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified projection assembly-input payload is selected from
the extractor/derivation decomposition of the forgetful theorem-shaped topology
statement.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified projection assembly-input payload also factors
through the explicit boundary finite-extinction input and the dependency-level
extraction/derivation payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation⟩) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified projection
assembly-input payload recovers the ordinary certified dependency projection
assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies =
      poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened projection route also exposes boundary finite extinction
together with the final extractor, its full topology derivation certificate,
and the lifted homeomorphism derivation certificate.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
      ExtinctionTopologyLiftedHomeomorphismDerivationForExtractionStatement.{u}
        extractSphere := by
  rcases
      topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
        dependencies with
    ⟨extractSphere, derivation, liftedDerivation⟩
  exact
    ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
      extractSphere, derivation, liftedDerivation⟩

/--
The strengthened lifted-homeomorphism projection assembly-input payload is
selected from the strengthened lifted extraction payload and paired with
boundary finite extinction.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection assembly-input payload is
selected from the lifted extraction/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
              (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation, liftedDerivation⟩
        exact
          ⟨finite_extinction_of_equation_boundary_dependencies dependencies,
            extractSphere, derivation, liftedDerivation⟩) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted-homeomorphism
projection assembly-input payload recovers the ordinary lifted-homeomorphism
dependency projection assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies =
      poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
projection assembly-input payload recovers the strengthened certified
extraction-derivation assembly-input payload.
-/
theorem poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    (by
      rcases
          poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
            dependencies with
        ⟨finiteExtinction, extractSphere, derivation,
          _liftedDerivation⟩
      exact ⟨finiteExtinction, extractSphere, derivation⟩) =
      poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies := by
  apply Subsingleton.elim

/--
The projection route exposes the final finite-extinction input,
post-extinction topology input, target statement, and universe-indexed
completion criterion through one named payload.
-/
theorem poincare_target_payload_of_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_projection_assembly_inputs_payload_of_dependencies
      dependencies with
    ⟨finiteExtinction, extraction⟩
  rcases poincare_payload_of_extinction_and_extraction
      finiteExtinction extraction with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extraction, target, criterion⟩

/--
The projection target payload is assembled from the named projection
assembly-input payload and the finite-extinction/extraction assembly bridge.
-/
theorem poincare_target_payload_of_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_dependency_projections dependencies =
      (by
        rcases poincare_projection_assembly_inputs_payload_of_dependencies
            dependencies with
          ⟨finiteExtinction, extraction⟩
        rcases poincare_payload_of_extinction_and_extraction
            finiteExtinction extraction with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The dependency projection target payload factors through the named
finite-extinction plus theorem-shaped topology-extraction assembly route.
-/
theorem poincare_target_payload_of_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_dependency_projections dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        let topologyStatement :=
          topology_extraction_statement_of_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_extraction_statement
            topologyStatement
        rcases poincare_payload_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The dependency projection target payload also factors through the final
extractor selected by the stored topology package.
-/
theorem poincare_target_payload_of_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_dependency_projections dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        rcases poincare_payload_of_extinction_and_extraction
            finiteExtinction extraction with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionTargetPayloads

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
projection target payload through the verification-family assembly inputs.
-/
theorem poincare_target_payload_of_dependency_projections_and_verification_family :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family
        dependencies verificationFamily with
    ⟨finiteExtinction, extraction⟩
  rcases poincare_payload_of_extinction_and_extraction
      finiteExtinction extraction with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extraction, target, criterion⟩

/--
The verification-family projection target payload is assembled from the named
verification-family projection assembly-input payload.
-/
theorem poincare_target_payload_of_dependency_projections_and_verification_family_eq :
    poincare_target_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_dependencies_and_verification_family
              dependencies verificationFamily with
          ⟨finiteExtinction, extraction⟩
        rcases poincare_payload_of_extinction_and_extraction
            finiteExtinction extraction with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The verification-family projection target payload is assembled from the named
finite-extinction and topology-extraction routes.
-/
theorem poincare_target_payload_of_dependency_projections_and_verification_family_to_projection_inputs_eq :
    poincare_target_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases poincare_payload_of_extinction_and_extraction
            (finite_extinction_of_dependencies_and_verification_family
              dependencies verificationFamily)
            (extinction_extraction_of_dependencies_and_verification_family
              dependencies verificationFamily) with
          ⟨target, criterion⟩
        exact
          ⟨ finite_extinction_of_dependencies_and_verification_family
              dependencies verificationFamily
          , extinction_extraction_of_dependencies_and_verification_family
              dependencies verificationFamily
          , target
          , criterion ⟩) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection target payload.
-/
theorem poincare_target_payload_of_dependency_projections_and_verification_family_to_dependencies_eq :
    poincare_target_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      poincare_target_payload_of_dependency_projections dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionTargetPayloads

/--
The projection route exposes the smoothability/surgery package inputs, a
certified final extractor, the target statement, and the completion criterion
through the extraction-derivation assembly route.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
      dependencies with
    ⟨_finiteExtinction, extractSphere, derivation⟩
  exact poincare_target_payload_of_surgery_and_extraction_derivation
    (smoothability_package_of_dependencies dependencies)
    (surgery_packages_of_dependencies dependencies)
    extractSphere derivation

/--
The certified extraction-derivation target payload is the surgery-plus-certified
extractor target payload selected from the named projection input payload.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies
            dependencies with
          ⟨_finiteExtinction, extractSphere, derivation⟩
        exact poincare_target_payload_of_surgery_and_extraction_derivation
          (smoothability_package_of_dependencies dependencies)
          (surgery_packages_of_dependencies dependencies)
          extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection target payload factors through the
extractor/derivation decomposition of the theorem-shaped topology extraction
statement.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finite_extinction_of_dependencies dependencies,
          extractSphere, derivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection target payload also factors through the
finite-extinction plus extractor/derivation topology assembly route.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finite_extinction_of_dependencies dependencies,
          extractSphere, derivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection target payload is also the payload carried
by the named dependency-level extraction/derivation route.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finite_extinction_of_dependencies dependencies,
          extractSphere, derivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection target payload also factors through the
extraction/derivation payload of the stored topology package.
-/
theorem poincare_target_payload_of_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finite_extinction_of_dependencies dependencies,
          extractSphere, derivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism projection route exposes finite extinction, a
certified final extractor, its lifted homeomorphism derivation certificate, the
target statement, and the completion criterion.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _liftedDerivation :
      ExtinctionTopologyLiftedHomeomorphismDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
        dependencies with
    ⟨finiteExtinction, extractSphere, derivation, liftedDerivation⟩
  rcases poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, derivation, liftedDerivation,
    target, criterion⟩

/--
The lifted-homeomorphism target payload is selected from the named lifted
projection assembly-input payload and the certified extraction assembly bridge.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_lifted_homeomorphism_derivation_dependencies
              dependencies with
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation,
          liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection target payload factors through
the lifted extraction/derivation decomposition of the dependency-level topology
statement.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection target payload factors through
the explicit finite-extinction input and named lifted extraction payload.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation,
          liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection target payload factors through
the lifted extraction/derivation payload of the stored topology package.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
              dependencies.topology with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation,
          liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism target payload
recovers the ordinary certified extraction-derivation target payload.
-/
theorem poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    (by
      rcases
          poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
            dependencies with
        ⟨finiteExtinction, extractSphere, derivation, _liftedDerivation,
          target, criterion⟩
      exact ⟨finiteExtinction, extractSphere, derivation, target,
        criterion⟩) =
      poincare_target_payload_of_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
The strengthened dependency projection route exposes the boundary finite
extinction input, the forgetful final extractor, the target statement, and the
universe-indexed completion criterion through one named payload.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
        dependencies with
    ⟨finiteExtinction, extraction⟩
  rcases poincare_payload_of_extinction_and_extraction
      finiteExtinction extraction with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extraction, target, criterion⟩

/--
The strengthened dependency projection target payload is assembled from the
boundary projection assembly-input payload and the final assembly bridge.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependency_projections
        dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨finiteExtinction, extraction⟩
        rcases poincare_payload_of_extinction_and_extraction
            finiteExtinction extraction with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection target payload factors through boundary
finite extinction and the theorem-shaped topology extraction statement after
forgetting equation-boundary data.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let topologyStatement :=
          topology_extraction_statement_of_dependencies
            (dependencies_of_equation_boundary_dependencies dependencies)
        let extraction :=
          extinction_implies_sphere_of_topology_extraction_statement
            topologyStatement
        rcases poincare_payload_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection target payload factors through the
ordinary stored-topology-package route after forgetting equation-boundary data.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependency_projections
        dependencies =
      poincare_target_payload_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened projection target payload
recovers the ordinary dependency projection target payload.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependency_projections
        dependencies =
      poincare_target_payload_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection target payload also factors through the
explicit boundary finite-extinction projection and the topology package's final
extractor.
-/
theorem poincare_target_payload_of_equation_boundary_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        let target :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extraction
        let criterion :=
          fun witness =>
            completionCriterionAtUniverse_of_poincareConjectureStatement
              witness target
        exact ⟨finiteExtinction, extraction, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection route exposes the boundary
finite-extinction input together with a certified final extractor, the target
statement, and the completion criterion.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
        dependencies with
    ⟨finiteExtinction, extractSphere, derivation⟩
  rcases poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, derivation, target, criterion⟩

/--
The strengthened certified dependency projection target payload is assembled
from the boundary certified projection assembly-input payload and the
finite-extinction/extraction-derivation bridge.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_equation_boundary_extraction_derivation_dependencies
              dependencies with
          ⟨finiteExtinction, extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection target payload factors through
the extractor/derivation decomposition of the forgetful theorem-shaped topology
statement.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection target payload also factors
through the explicit boundary finite-extinction input and the dependency-level
extraction/derivation payload.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation, target,
            criterion⟩) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified projection
target payload recovers the ordinary certified dependency projection target
payload.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      poincare_target_payload_of_extraction_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified projection target payload agrees with the direct
boundary-package certified extraction-derivation route.
-/
theorem poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
            dependencies.smoothability dependencies.surgery dependencies.topology
        exact
          ⟨finite_extinction_input_of_smoothability_and_boundary_surgery_packages
              dependencies.smoothability dependencies.surgery,
            extractSphere, derivation, target,
            fun witness =>
              completionCriterionAtUniverse_of_poincareConjectureStatement
                witness target⟩) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection route exposes boundary finite
extinction, a certified final extractor, its lifted homeomorphism derivation
certificate, the target statement, and the completion criterion.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _liftedDerivation :
      ExtinctionTopologyLiftedHomeomorphismDerivationForExtractionStatement.{u}
        extractSphere,
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
        dependencies with
    ⟨finiteExtinction, extractSphere, derivation, liftedDerivation⟩
  rcases poincare_payload_of_finite_extinction_and_extraction_derivation
      finiteExtinction extractSphere derivation with
    ⟨target, criterion⟩
  exact ⟨finiteExtinction, extractSphere, derivation, liftedDerivation,
    target, criterion⟩

/--
The strengthened lifted-homeomorphism target payload is selected from the
boundary lifted projection assembly-input payload and the certified extraction
assembly bridge.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_projection_assembly_inputs_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependencies
              dependencies with
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact ⟨finiteExtinction, extractSphere, derivation,
          liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism target payload factors through the
lifted extraction/derivation decomposition of the forgetful theorem-shaped
topology statement.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
              (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation, liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            finiteExtinction extractSphere derivation with
          ⟨target, criterion⟩
        exact
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation, target, criterion⟩) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted-homeomorphism
target payload recovers the ordinary lifted-homeomorphism dependency projection
target payload.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
target payload recovers the strengthened certified extraction-derivation target
payload.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    (by
      rcases
          poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
            dependencies with
        ⟨finiteExtinction, extractSphere, derivation, _liftedDerivation,
          target, criterion⟩
      exact ⟨finiteExtinction, extractSphere, derivation, target,
        criterion⟩) =
      poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
target payload and choosing the direct boundary target recovers the direct
boundary-package certified extraction-derivation route.
-/
theorem poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_input_of_smoothability_and_boundary_surgery_packages
            dependencies.smoothability dependencies.surgery
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
              dependencies.topology with
          ⟨extractSphere, derivation, liftedDerivation⟩
        let target :=
          poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
            dependencies.smoothability dependencies.surgery dependencies.topology
        exact
          ⟨finiteExtinction, extractSphere, derivation,
            liftedDerivation, target,
            fun witness =>
              completionCriterionAtUniverse_of_poincareConjectureStatement
                witness target⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the explicit packages, final assembly
inputs, and target statement through the projection route.
-/
theorem poincare_full_assembly_payload_of_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
    ∃ _topologyPackage : ExtinctionTopologyExtractionPackage.{u},
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
    ∃ _extractSphere : ExtinctionImpliesSphereStatement.{u},
      PoincareConjectureStatement.{u} := by
  rcases poincare_target_payload_of_dependency_projections dependencies with
    ⟨finiteExtinction, extraction, target, _criterion⟩
  exact ⟨smoothability_package_of_dependencies dependencies,
    surgery_packages_of_dependencies dependencies,
    topology_package_of_dependencies dependencies,
    finiteExtinction,
    extraction,
    target⟩

/--
The projection full-assembly payload is selected from the named projection
target payload together with the stored dependency packages.
-/
theorem poincare_full_assembly_payload_of_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_dependency_projections dependencies =
      (by
        rcases poincare_target_payload_of_dependency_projections
            dependencies with
          ⟨finiteExtinction, extraction, target, _criterion⟩
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          topology_package_of_dependencies dependencies,
          finiteExtinction,
          extraction,
          target⟩) := by
  apply Subsingleton.elim

/--
The dependency projection full-assembly payload factors through the named
finite-extinction plus theorem-shaped topology-extraction endpoint.
-/
theorem poincare_full_assembly_payload_of_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_dependency_projections dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        let topologyStatement :=
          topology_extraction_statement_of_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_extraction_statement
            topologyStatement
        let target :=
          poincare_statement_of_finite_extinction_and_topology_extraction_statement
            finiteExtinction topologyStatement
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          topology_package_of_dependencies dependencies,
          finiteExtinction,
          extraction,
          target⟩) := by
  apply Subsingleton.elim

/--
The dependency projection full-assembly payload factors through the final
extractor selected by the stored topology package.
-/
theorem poincare_full_assembly_payload_of_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_dependency_projections dependencies =
      (by
        let finiteExtinction := finite_extinction_of_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        let target :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extraction
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          dependencies.topology,
          finiteExtinction,
          extraction,
          target⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the explicit smoothability/surgery
packages, a certified final extractor, and the target statement through the
extraction-derivation projection route.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _smoothabilityPackage : SmoothabilityPackage.{u},
    ∃ _surgeryPackages :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)),
    ∃ extractSphere : ExtinctionImpliesSphereStatement.{u},
    ∃ _derivation :
      ExtinctionTopologyDerivationForExtractionStatement.{u}
        extractSphere,
      PoincareConjectureStatement.{u} := by
  rcases poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies with
    ⟨_finiteExtinction, extractSphere, derivation, target,
      _criterion⟩
  exact ⟨smoothability_package_of_dependencies dependencies,
    surgery_packages_of_dependencies dependencies,
    extractSphere, derivation, target⟩

/--
The certified extraction-derivation full-assembly payload is selected from the
named certified target payload together with the stored dependency packages.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            poincare_target_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨_finiteExtinction, extractSphere, derivation, target,
            _criterion⟩
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection full-assembly payload factors through the
extractor/derivation decomposition of the theorem-shaped topology extraction
statement.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection full-assembly payload factors through the
finite-extinction plus extractor/derivation endpoint.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection full-assembly payload is also carried by
the named dependency-level extraction/derivation route.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection full-assembly payload factors through the
extraction/derivation payload of the stored topology package.
-/
theorem poincare_full_assembly_payload_of_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_full_assembly_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        let target :=
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation
        exact ⟨smoothability_package_of_dependencies dependencies,
          surgery_packages_of_dependencies dependencies,
          extractSphere, derivation, target⟩) := by
  apply Subsingleton.elim

/--
A completed dependency package supplies the two theorem-shaped inputs consumed
by the final finite-extinction/topology-extraction assembly theorem, through
the named projection-route assembly-input payload.
-/
theorem poincare_assembly_inputs_payload_of_dependencies
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _finiteExtinction :
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          FiniteExtinctionByRicciFlowWithSurgery M),
      ExtinctionImpliesSphereStatement.{u} := by
  exact poincare_projection_assembly_inputs_payload_of_dependencies
    dependencies

/--
The final assembly-input payload is the named projection assembly-input
payload.
-/
theorem poincare_assembly_inputs_payload_of_dependencies_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_assembly_inputs_payload_of_dependencies dependencies =
      poincare_projection_assembly_inputs_payload_of_dependencies
        dependencies := by
  apply Subsingleton.elim

/--
The projection-based dependency route exposes the local target and
universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_dependency_projections dependencies with
    ⟨_finiteExtinction, _extraction, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The projection completion payload is selected from the named projection target
payload.
-/
theorem poincare_completion_payload_of_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_dependency_projections dependencies =
      (by
        rcases poincare_target_payload_of_dependency_projections
            dependencies with
          ⟨_finiteExtinction, _extraction, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The dependency projection completion payload is the payload of the named
finite-extinction plus theorem-shaped topology-extraction route.
-/
theorem poincare_completion_payload_of_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_dependency_projections dependencies =
      poincare_payload_of_finite_extinction_and_topology_extraction_statement
        (finite_extinction_of_dependencies dependencies)
        (topology_extraction_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The dependency projection completion payload is the payload of the final
extractor selected by the stored topology package.
-/
theorem poincare_completion_payload_of_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_dependency_projections dependencies =
      poincare_payload_of_extinction_and_extraction
        (finite_extinction_of_dependencies dependencies)
        (extinction_implies_sphere_of_topology_package
          dependencies.topology) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionCompletionPayloads

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
final target and completion criterion through the verification-family
projection target payload.
-/
theorem poincare_completion_payload_of_dependency_projections_and_verification_family :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily with
    ⟨_finiteExtinction, _extraction, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The verification-family completion payload is selected from the named
verification-family projection target payload.
-/
theorem poincare_completion_payload_of_dependency_projections_and_verification_family_eq :
    poincare_completion_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases
            poincare_target_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨_finiteExtinction, _extraction, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The verification-family completion payload factors through the named
verification-family target-payload route.
-/
theorem poincare_completion_payload_of_dependency_projections_and_verification_family_to_target_payload_eq :
    poincare_completion_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases
            poincare_target_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨_finiteExtinction, _extraction, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection completion payload.
-/
theorem poincare_completion_payload_of_dependency_projections_and_verification_family_to_dependencies_eq :
    poincare_completion_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      poincare_completion_payload_of_dependency_projections dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionCompletionPayloads

/--
The extraction-derivation projection route exposes the local target and
universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_extraction_derivation_dependency_projections
      dependencies with
    ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The certified extraction-derivation completion payload is selected from the
named certified target payload.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            poincare_target_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion payload is selected from the
extractor/derivation decomposition of the theorem-shaped topology extraction
statement.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion payload is the payload of the
named finite-extinction plus extractor/derivation route.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion payload is also carried by the
named dependency-level extraction/derivation route.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion payload is the payload carried
by the extraction/derivation route selected from the stored topology package.
-/
theorem poincare_completion_payload_of_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism projection route exposes the local target and
universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨_finiteExtinction, _extractSphere, _derivation, _liftedDerivation,
      target, criterion⟩
  exact ⟨target, criterion⟩

/--
The lifted-homeomorphism completion payload is selected from the named lifted
target payload.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_target_payload_of_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨_finiteExtinction, _extractSphere, _derivation,
            _liftedDerivation, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion payload is the
payload carried by the lifted extraction/derivation decomposition of the
dependency-level topology statement.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion payload is carried by
the explicit finite-extinction input and named lifted extraction payload.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion payload is the payload
carried by the lifted extraction/derivation route selected from the stored
topology package.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism completion
payload recovers the ordinary certified extraction-derivation completion
payload.
-/
theorem poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_completion_payload_of_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
The strengthened dependency projection route exposes the local target and
universe-indexed completion criterion through the boundary target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases poincare_target_payload_of_equation_boundary_dependency_projections
      dependencies with
    ⟨_finiteExtinction, _extraction, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The strengthened dependency projection completion payload is selected from the
named boundary projection target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies =
      (by
        rcases
            poincare_target_payload_of_equation_boundary_dependency_projections
              dependencies with
          ⟨_finiteExtinction, _extraction, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection completion payload is the payload of the
boundary finite-extinction plus forgetful theorem-shaped topology-extraction
route.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies =
      poincare_payload_of_finite_extinction_and_topology_extraction_statement
        (finite_extinction_of_equation_boundary_dependencies dependencies)
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies)) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection completion payload factors through the
ordinary stored-topology-package route after forgetting equation-boundary data.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies =
      poincare_completion_payload_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened projection completion
payload recovers the ordinary dependency projection completion payload.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies =
      poincare_completion_payload_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection completion payload also factors through
the explicit boundary finite-extinction projection and the topology package's
final extractor.
-/
theorem poincare_completion_payload_of_equation_boundary_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        let target :=
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extraction
        exact
          ⟨target,
            fun witness =>
              completionCriterionAtUniverse_of_poincareConjectureStatement
                witness target⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection route exposes the local target
and universe-indexed completion criterion through the boundary certified target
payload.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies with
    ⟨_finiteExtinction, _extractSphere, _derivation, target, criterion⟩
  exact ⟨target, criterion⟩

/--
The strengthened certified dependency projection completion payload is selected
from the named boundary certified projection target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections
              dependencies with
          ⟨_finiteExtinction, _extractSphere, _derivation, target,
            criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection completion payload is the
payload selected from the extractor/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection completion payload also
factors through the explicit boundary finite-extinction input and the
dependency-level extraction/derivation payload.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified projection
completion payload recovers the ordinary certified dependency projection
completion payload.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      poincare_completion_payload_of_extraction_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified projection completion payload agrees with projecting
the target and criterion from the direct boundary-package certified route.
-/
theorem poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      ⟨poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology,
        fun witness =>
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
              dependencies.smoothability dependencies.surgery
              dependencies.topology)⟩ := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection route exposes the local
target and universe-indexed completion criterion through the boundary lifted
target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  rcases
      poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨_finiteExtinction, _extractSphere, _derivation, _liftedDerivation,
      target, criterion⟩
  exact ⟨target, criterion⟩

/--
The strengthened lifted-homeomorphism completion payload is selected from the
named boundary lifted target payload.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_target_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨_finiteExtinction, _extractSphere, _derivation,
            _liftedDerivation, target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism completion payload is the payload carried
by the lifted extraction/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted-homeomorphism
completion payload recovers the ordinary lifted-homeomorphism dependency
projection completion payload.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
completion payload recovers the strengthened certified extraction-derivation
completion payload.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism completion payload agrees with the
direct boundary-package certified extraction-derivation route.
-/
theorem poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      ⟨poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology,
        fun witness =>
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
              dependencies.smoothability dependencies.surgery
              dependencies.topology)⟩ := by
  apply Subsingleton.elim

/--
The aggregate dependency package also proves the Poincare target through the
full finite-extinction and post-extinction extraction projection payload.
-/
theorem poincare_statement_of_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_completion_payload_of_dependency_projections dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The projection Poincare statement is selected from the named projection
completion payload.
-/
theorem poincare_statement_of_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_dependency_projections dependencies =
      (by
        rcases poincare_completion_payload_of_dependency_projections
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The dependency projection Poincare statement is the target of the named
finite-extinction plus theorem-shaped topology-extraction route.
-/
theorem poincare_statement_of_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_dependency_projections dependencies =
      poincare_statement_of_finite_extinction_and_topology_extraction_statement
        (finite_extinction_of_dependencies dependencies)
        (topology_extraction_statement_of_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The dependency projection Poincare statement is the target of the final
extractor selected by the stored topology package.
-/
theorem poincare_statement_of_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_dependency_projections dependencies =
      poincare_statement_of_extinction_and_extraction
        (finite_extinction_of_dependencies dependencies)
        (extinction_implies_sphere_of_topology_package
          dependencies.topology) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionStatements

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
Poincare target statement through the verification-family completion payload.
-/
theorem poincare_statement_of_dependency_projections_and_verification_family :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily with
    ⟨target, _criterion⟩
  exact target

/--
The verification-family Poincare statement is selected from the named
verification-family completion payload.
-/
theorem poincare_statement_of_dependency_projections_and_verification_family_eq :
    poincare_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases
            poincare_completion_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The verification-family Poincare statement factors through the named
verification-family completion payload.
-/
theorem poincare_statement_of_dependency_projections_and_verification_family_to_completion_payload_eq :
    poincare_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      (by
        rcases
            poincare_completion_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection Poincare statement.
-/
theorem poincare_statement_of_dependency_projections_and_verification_family_to_dependencies_eq :
    poincare_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      poincare_statement_of_dependency_projections dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionStatements

/--
The aggregate dependency package also proves the Poincare target through the
certified extraction-derivation projection payload.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_extraction_derivation_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The certified extraction-derivation projection Poincare statement is selected
from the named certified completion payload.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            poincare_completion_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The certified dependency projection Poincare statement is the target selected
from the extractor/derivation decomposition of the theorem-shaped topology
extraction statement.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection Poincare statement is the target of the
named finite-extinction plus extractor/derivation route.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection Poincare statement is also carried by the
named dependency-level extraction/derivation route.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The certified dependency projection Poincare statement is the target carried by
the extraction/derivation route selected from the stored topology package.
-/
theorem poincare_statement_of_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The aggregate dependency package also proves the Poincare target through the
lifted-homeomorphism certified projection payload.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The lifted-homeomorphism projection Poincare statement is selected from the
named lifted completion payload.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection Poincare statement is the target
carried by the lifted extraction/derivation decomposition of the
dependency-level topology statement.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection Poincare statement is the target
carried by the explicit finite-extinction input and named lifted extraction
payload.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection Poincare statement is the target
carried by the extraction/derivation route selected from the stored topology
package.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism Poincare
statement route recovers the ordinary certified extraction-derivation Poincare
statement route.
-/
theorem poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_statement_of_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
The strengthened dependency projection route proves the Poincare target through
the boundary projection completion payload.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened dependency projection Poincare statement is selected from the
named boundary projection completion payload.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependency_projections
        dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_dependency_projections
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection Poincare statement is the target of the
boundary finite-extinction plus forgetful theorem-shaped topology-extraction
route.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependency_projections
        dependencies =
      poincare_statement_of_finite_extinction_and_topology_extraction_statement
        (finite_extinction_of_equation_boundary_dependencies dependencies)
        (topology_extraction_statement_of_dependencies
          (dependencies_of_equation_boundary_dependencies dependencies)) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection Poincare statement is the target of the
final extractor selected by the stored topology package.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependency_projections
        dependencies =
      poincare_statement_of_extinction_and_extraction
        (finite_extinction_of_equation_boundary_dependencies dependencies)
        (extinction_implies_sphere_of_topology_package
          dependencies.topology) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened projection Poincare
statement recovers the ordinary dependency projection Poincare statement.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependency_projections
        dependencies =
      poincare_statement_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened dependency projection Poincare statement also factors through
the explicit boundary finite-extinction projection and the topology package's
final extractor.
-/
theorem poincare_statement_of_equation_boundary_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          poincare_statement_of_extinction_and_extraction
            finiteExtinction extraction) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection route proves the Poincare
target through the boundary certified projection completion payload.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened certified dependency projection Poincare statement is selected
from the named boundary certified projection completion payload.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection Poincare statement is the
target selected from the extractor/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
The strengthened certified dependency projection Poincare statement also
factors through the explicit finite-extinction input and the dependency-level
extraction/derivation payload.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified projection
Poincare statement recovers the ordinary certified dependency projection
Poincare statement.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      poincare_statement_of_extraction_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified projection Poincare statement agrees with the direct
boundary-package certified extraction-derivation statement route.
-/
theorem poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection route proves the Poincare
target through the boundary lifted completion payload.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    PoincareConjectureStatement.{u} := by
  rcases
      poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨target, _criterion⟩
  exact target

/--
The strengthened lifted-homeomorphism Poincare statement is selected from the
named boundary lifted completion payload.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism Poincare statement is the target carried
by the lifted extraction/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation⟩
        exact
          poincare_statement_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted-homeomorphism
Poincare statement recovers the ordinary lifted-homeomorphism dependency
projection Poincare statement.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
Poincare statement recovers the strengthened certified extraction-derivation
Poincare statement.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
Poincare statement recovers the direct boundary-package certified
extraction-derivation statement route.
-/
theorem poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The projection-based dependency route exposes the canonical mathlib-shaped
topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_dependency_projections dependencies)

/--
The projection canonical topological sphere statement is the canonical bridge
applied to the named projection Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_dependency_projections dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_dependency_projections dependencies) := by
  apply Subsingleton.elim

/--
The dependency projection canonical topological statement factors through the
finite-extinction plus theorem-shaped topology-extraction Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_dependency_projections dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_finite_extinction_and_topology_extraction_statement
          (finite_extinction_of_dependencies dependencies)
          (topology_extraction_statement_of_dependencies dependencies)) := by
  apply Subsingleton.elim

/--
The dependency projection canonical topological statement factors through the
final extractor selected by the stored topology package.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_dependency_projections dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_extinction_and_extraction
          (finite_extinction_of_dependencies dependencies)
          (extinction_implies_sphere_of_topology_package
            dependencies.topology)) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionCanonicalStatements

variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications expose the
canonical mathlib-shaped topological 3-sphere statement through the
verification-family Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_and_verification_family :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_dependency_projections_and_verification_family
      dependencies verificationFamily)

/--
The verification-family canonical topological statement is the canonical bridge
applied to the named verification-family Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_and_verification_family_eq :
    canonical_three_sphere_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_dependency_projections_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
The verification-family canonical topological statement factors through the
named verification-family Poincare statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_and_verification_family_to_statement_eq :
    canonical_three_sphere_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_dependency_projections_and_verification_family
          dependencies verificationFamily) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection canonical statement.
-/
theorem canonical_three_sphere_statement_of_dependency_projections_and_verification_family_to_dependencies_eq :
    canonical_three_sphere_statement_of_dependency_projections_and_verification_family
        dependencies verificationFamily =
      canonical_three_sphere_statement_of_dependency_projections
        dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionCanonicalStatements

/--
The certified extraction-derivation projection route exposes the canonical
mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_extraction_derivation_dependency_projections
      dependencies)

/--
The certified extraction-derivation canonical topological sphere statement is
the canonical bridge applied to the named certified Poincare statement.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_extraction_derivation_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation dependency projection canonical statement
factors through the extractor/derivation decomposition of the theorem-shaped
topology extraction statement.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation dependency projection canonical topological
statement factors through the finite-extinction plus extractor/derivation
Poincare statement.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation dependency projection canonical statement
is also carried by the named dependency-level extraction/derivation route.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The certified extraction-derivation dependency projection canonical topological
statement factors through the extraction/derivation payload selected from the
stored topology package.
-/
theorem canonical_three_sphere_statement_of_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism projection route exposes the canonical mathlib-shaped
topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependencies.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies)

/--
The lifted-homeomorphism canonical topological sphere statement is the canonical
bridge applied to the named lifted Poincare statement.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_lifted_homeomorphism_derivation_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism canonical topological statement factors through the
lifted extraction/derivation decomposition of the dependency-level topology
statement.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism canonical topological statement factors through the
explicit finite-extinction input and named lifted extraction payload.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism canonical topological statement factors through the
extraction/derivation payload selected from the stored topology package.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies =
      (by
        rcases topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism canonical route
recovers the ordinary certified extraction-derivation canonical route.
-/
theorem canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependencies.{u}) :
    canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
      dependencies =
      canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary projection route exposes the canonical
mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_equation_boundary_dependency_projections
      dependencies)

/--
The strengthened equation-boundary canonical topological statement is the
canonical bridge applied to the named boundary projection Poincare statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_equation_boundary_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary canonical statement factors through the
finite-extinction plus theorem-shaped topology-extraction route.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections_to_topology_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_finite_extinction_and_topology_extraction_statement
          (finite_extinction_of_equation_boundary_dependencies dependencies)
          (topology_extraction_statement_of_dependencies
            (dependencies_of_equation_boundary_dependencies
              dependencies))) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary canonical statement factors through the
final extractor selected by the stored topology package.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_extinction_and_extraction
          (finite_extinction_of_equation_boundary_dependencies dependencies)
          (extinction_implies_sphere_of_topology_package
            dependencies.topology)) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened canonical statement
recovers the ordinary projection canonical statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary canonical statement also factors through the
explicit boundary finite-extinction projection and the topology package's final
extractor.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_dependency_projections
        dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_extinction_and_extraction
              finiteExtinction extraction)) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary projection route exposes the
canonical mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
      dependencies)

/--
The strengthened certified equation-boundary canonical statement is the
canonical bridge applied to the named boundary certified Poincare statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_equation_boundary_extraction_derivation_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary canonical statement factors
through the extractor/derivation decomposition of the forgetful theorem-shaped
topology statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary canonical statement factors
through the explicit finite-extinction input and the dependency-level
extraction/derivation payload.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary canonical statement is also
carried by the named dependency-level extraction/derivation route.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary canonical statement factors
through the extraction/derivation payload selected from the stored topology
package.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified canonical
statement recovers the ordinary certified projection canonical statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_extraction_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified projection canonical statement agrees with the direct
boundary-package certified extraction-derivation canonical route.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection route exposes the canonical
mathlib-shaped topological 3-sphere statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
      dependencies)

/--
The strengthened lifted-homeomorphism canonical statement is the canonical
bridge applied to the named boundary lifted Poincare statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
          dependencies) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism canonical statement is the target carried
by the lifted extraction/derivation decomposition of the forgetful
theorem-shaped topology statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism canonical statement factors through the
explicit finite-extinction input and the dependency-level extraction/derivation
payload.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism canonical statement factors through the
extraction/derivation payload selected from the stored topology package.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation⟩
        exact
          canonical_three_sphere_statement_of_poincare_statement
            (poincare_statement_of_finite_extinction_and_extraction_derivation
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              extractSphere derivation)) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted-homeomorphism
canonical statement recovers the ordinary lifted-homeomorphism dependency
projection canonical statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_forgetful_dependencies_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_lifted_homeomorphism_derivation_dependency_projections
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
canonical statement recovers the strengthened certified extraction-derivation
canonical statement.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
canonical statement recovers the direct boundary-package certified
extraction-derivation canonical route.
-/
theorem canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_boundary_route_eq
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    canonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies =
      canonical_three_sphere_statement_of_boundary_surgery_and_topology_package_extraction_derivation
        dependencies.smoothability dependencies.surgery dependencies.topology := by
  apply Subsingleton.elim

/--
The projection-based assembly route also discharges the explicit
universe-indexed completion criterion.
-/
theorem completion_criterion_of_dependency_projections
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_completion_payload_of_dependency_projections dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The projection completion criterion is selected from the named projection
completion payload.
-/
theorem completion_criterion_of_dependency_projections_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_dependency_projections witness dependencies =
      (by
        rcases poincare_completion_payload_of_dependency_projections
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The dependency projection completion criterion is the criterion carried by the
finite-extinction plus theorem-shaped topology-extraction endpoint.
-/
theorem completion_criterion_of_dependency_projections_to_topology_statement_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_dependency_projections witness dependencies =
      (by
        rcases
            poincare_payload_of_finite_extinction_and_topology_extraction_statement
              (finite_extinction_of_dependencies dependencies)
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The dependency projection completion criterion is carried by the final
extractor selected from the stored topology package.
-/
theorem completion_criterion_of_dependency_projections_to_package_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_dependency_projections witness dependencies =
      (by
        rcases
            poincare_payload_of_extinction_and_extraction
              (finite_extinction_of_dependencies dependencies)
              (extinction_implies_sphere_of_topology_package
                dependencies.topology) with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

section VerificationFamilyProjectionCriteria

variable (witness : Type u)
variable (dependencies : PoincareProofDependencies.{u})
variable (verificationFamily :
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M),
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package payload.2)))

include witness dependencies verificationFamily

/--
Ordinary aggregate dependencies plus explicit equation verifications discharge
the universe-indexed completion criterion through the verification-family
completion payload.
-/
theorem completion_criterion_of_dependency_projections_and_verification_family :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_dependency_projections_and_verification_family
        dependencies verificationFamily with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The verification-family completion criterion is selected from the named
verification-family completion payload.
-/
theorem completion_criterion_of_dependency_projections_and_verification_family_eq :
    completion_criterion_of_dependency_projections_and_verification_family
        witness dependencies verificationFamily =
      (by
        rcases
            poincare_completion_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The verification-family completion criterion factors through the named
verification-family completion payload.
-/
theorem completion_criterion_of_dependency_projections_and_verification_family_to_completion_payload_eq :
    completion_criterion_of_dependency_projections_and_verification_family
        witness dependencies verificationFamily =
      (by
        rcases
            poincare_completion_payload_of_dependency_projections_and_verification_family
              dependencies verificationFamily with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
Forgetting the verification-family lift recovers the ordinary dependency
projection completion criterion.
-/
theorem completion_criterion_of_dependency_projections_and_verification_family_to_dependencies_eq :
    completion_criterion_of_dependency_projections_and_verification_family
        witness dependencies verificationFamily =
      completion_criterion_of_dependency_projections witness dependencies := by
  apply Subsingleton.elim

end VerificationFamilyProjectionCriteria

/--
The certified extraction-derivation projection route also discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_extraction_derivation_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The certified extraction-derivation completion criterion is selected from the
named certified completion payload.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_extraction_derivation_dependency_projections
            dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion criterion is selected from the
extractor/derivation decomposition of the theorem-shaped topology extraction
statement.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections_to_statement_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion criterion is the criterion
carried by the finite-extinction plus extractor/derivation endpoint.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion criterion is also carried by
the named dependency-level extraction/derivation route.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections_to_extraction_derivation_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_dependencies
            dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The certified dependency projection completion criterion is carried by the
extraction/derivation payload selected from the stored topology package.
-/
theorem completion_criterion_of_extraction_derivation_dependency_projections_to_package_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_extraction_derivation_dependency_projections
      witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism projection route also discharges the explicit
universe-indexed completion criterion.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The lifted-homeomorphism completion criterion is selected from the named
lifted projection completion payload.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion criterion is carried
by the lifted decomposition of the dependency-level topology statement.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies dependencies) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion criterion is carried
by the explicit finite-extinction input and named lifted extraction payload.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
      witness dependencies =
      (by
        rcases
            topology_extraction_lifted_homeomorphism_derivation_payload_of_dependencies
              dependencies with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The lifted-homeomorphism dependency projection completion criterion is carried by
the extraction/derivation payload selected from the stored topology package.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
      witness dependencies =
      (by
        rcases topology_extraction_lifted_homeomorphism_derivation_payload_of_topology_package
            dependencies.topology with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the lifted-homeomorphism completion
criterion recovers the certified extraction-derivation completion criterion.
-/
theorem completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (witness : Type u) (dependencies : PoincareProofDependencies.{u}) :
    completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
      witness dependencies =
      completion_criterion_of_extraction_derivation_dependency_projections
        witness dependencies := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary projection route also discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_equation_boundary_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The strengthened equation-boundary completion criterion is selected from the
named boundary projection completion payload.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependency_projections
        witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_dependency_projections
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary completion criterion is carried by the
finite-extinction plus theorem-shaped topology-extraction endpoint.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections_to_topology_statement_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependency_projections
        witness dependencies =
      (by
        rcases
            poincare_payload_of_finite_extinction_and_topology_extraction_statement
              (finite_extinction_of_equation_boundary_dependencies dependencies)
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary completion criterion factors through the
ordinary stored-topology-package route after forgetting equation-boundary data.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections_to_package_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependency_projections
        witness dependencies =
      completion_criterion_of_dependency_projections witness
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened completion criterion
recovers the ordinary projection completion criterion.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections_to_forgetful_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependency_projections
        witness dependencies =
      completion_criterion_of_dependency_projections witness
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened equation-boundary completion criterion also factors through
the explicit boundary finite-extinction projection and the topology package's
final extractor.
-/
theorem completion_criterion_of_equation_boundary_dependency_projections_to_finite_extinction_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_dependency_projections
        witness dependencies =
      (by
        let finiteExtinction :=
          finite_extinction_of_equation_boundary_dependencies dependencies
        let extraction :=
          extinction_implies_sphere_of_topology_package dependencies.topology
        exact
          completionCriterionAtUniverse_of_poincareConjectureStatement
            witness
            (poincare_statement_of_extinction_and_extraction
              finiteExtinction extraction)) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary projection route also discharges
the explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The strengthened certified equation-boundary completion criterion is selected
from the named boundary certified projection completion payload.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary completion criterion is carried
by the extractor/derivation decomposition of the forgetful theorem-shaped
topology statement.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections_to_statement_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened certified equation-boundary completion criterion also factors
through the explicit finite-extinction input and the dependency-level
extraction/derivation payload.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections_to_finite_extinction_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened certified completion
criterion recovers the ordinary certified projection completion criterion.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections_to_forgetful_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies =
      completion_criterion_of_extraction_derivation_dependency_projections
        witness
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
The strengthened certified projection completion criterion agrees with the
direct boundary-package certified extraction-derivation statement route.
-/
theorem completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections_to_boundary_route_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies =
      completionCriterionAtUniverse_of_poincareConjectureStatement
        witness
        (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
          dependencies.smoothability dependencies.surgery dependencies.topology) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism projection route also discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases
      poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        dependencies with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The strengthened lifted-homeomorphism completion criterion is selected from
the named boundary lifted projection completion payload.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            poincare_completion_payload_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
              dependencies with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The strengthened lifted-homeomorphism completion criterion is carried by the
lifted decomposition of the forgetful theorem-shaped topology statement.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_statement_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            extinction_topology_extraction_statement_iff_extraction_with_lifted_homeomorphism_derivation.mp
              (topology_extraction_statement_of_dependencies
                (dependencies_of_equation_boundary_dependencies
                  dependencies)) with
          ⟨extractSphere, derivation, _liftedDerivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_finite_extinction_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      (by
        rcases
            topology_extraction_derivation_payload_of_equation_boundary_dependencies
              dependencies with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_package_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      (by
        rcases topology_extraction_derivation_payload_of_topology_package
            (dependencies_of_equation_boundary_dependencies dependencies).topology with
          ⟨extractSphere, derivation⟩
        rcases poincare_payload_of_finite_extinction_and_extraction_derivation
            (finite_extinction_of_equation_boundary_dependencies dependencies)
            extractSphere derivation with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
Forgetting equation-boundary data in the strengthened lifted completion
criterion recovers the ordinary lifted dependency projection completion
criterion.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_forgetful_dependencies_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      completion_criterion_of_lifted_homeomorphism_derivation_dependency_projections
        witness
        (dependencies_of_equation_boundary_dependencies dependencies) := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted completion
criterion recovers the strengthened certified extraction-derivation completion
criterion.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_extraction_derivation_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections
        witness dependencies := by
  apply Subsingleton.elim

/--
Forgetting the lifted certificate in the strengthened lifted-homeomorphism
completion criterion recovers the direct boundary-package certified
extraction-derivation criterion route.
-/
theorem completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections_to_boundary_route_eq
    (witness : Type u)
    (dependencies : PoincareProofDependenciesWithEquationBoundary.{u}) :
    completion_criterion_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections
        witness dependencies =
      completionCriterionAtUniverse_of_poincareConjectureStatement
        witness
        (poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation
          dependencies.smoothability dependencies.surgery dependencies.topology) := by
  apply Subsingleton.elim

end Poincare
