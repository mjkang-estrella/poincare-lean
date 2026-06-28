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
Recognition as `ThreeSphere` gives the same transported smoothability and
surgery-model prerequisites by first converting the recognized sphere to the
one-point compactification model.  This is the smoothability-side consumer
route for topology packages whose final output is stated as a sphere
homeomorphism.
-/
theorem smoothability_surgery_prerequisites_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
    ∃ _smooth : IsManifold ThreeManifoldModelWithCorners 1 M,
      Nonempty M :=
  smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

end Poincare
