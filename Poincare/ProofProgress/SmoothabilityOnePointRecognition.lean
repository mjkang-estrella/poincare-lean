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
One-point recognition supplies a single transported charted-space witness that
simultaneously carries the `C∞` smooth-manifold proof, the regularity-lowered
`C¹` surgery-model proof, and the topological prerequisites used by the
surgery layer.
-/
theorem smoothability_transported_smooth_and_surgery_model_package_of_homeomorph_to_onePoint_threeSpace
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M) ∧
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ _t2 : T2Space M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        Nonempty M := by
  rcases h with ⟨e⟩
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  have smooth :
      letI : ChartedSpace ThreeManifoldModel M := charted
      IsManifold (𝓡 3) ∞ M := by
    exact homeomorphToOnePoint_threeSpace_smoothManifold e
  have surgeryModel :
      letI : ChartedSpace ThreeManifoldModel M := charted
      IsManifold ThreeManifoldModelWithCorners 1 M := by
    exact homeomorphToOnePoint_threeSpace_surgeryModel_isManifold e
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      ⟨e⟩ with
    ⟨t2, _charted, simple, compact, _smooth, nonempty⟩
  exact ⟨charted, smooth, surgeryModel, t2, simple, compact, nonempty⟩

/--
One-point recognition closes the theorem-shaped transported smoothability
bridge: it supplies the transported charted-space witness and the corresponding
surgery-model manifold evidence for every recognized compact simply connected
source.
-/
theorem smoothabilityTransportedBridgeStatement_of_onePointRecognition :
    SmoothabilityTransportedBridgeStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases h with ⟨e⟩
  refine ⟨homeomorphToOnePoint_threeSpace_smoothChartedSpace e, ?_⟩
  exact homeomorphToOnePoint_threeSpace_surgeryModel_isManifold e

/--
One-point recognition also closes the transported `C∞` smooth-manifold
statement before lowering regularity to the surgery model.
-/
theorem smoothabilityTransportedSmoothManifoldStatement_of_onePointRecognition :
    SmoothabilityTransportedSmoothManifoldStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases h with ⟨e⟩
  refine ⟨homeomorphToOnePoint_threeSpace_smoothChartedSpace e, ?_⟩
  exact homeomorphToOnePoint_threeSpace_smoothManifold e

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

/--
Sphere recognition gives the same synchronized transported smoothability
package after converting the sphere recognition homeomorphism to the one-point
compactification model.
-/
theorem smoothability_transported_smooth_and_surgery_model_package_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold (𝓡 3) ∞ M) ∧
      (letI : ChartedSpace ThreeManifoldModel M := charted
       IsManifold ThreeManifoldModelWithCorners 1 M) ∧
      ∃ _t2 : T2Space M,
      ∃ _simple : SimplyConnectedSpace M,
      ∃ _compact : CompactSpace M,
        Nonempty M :=
  smoothability_transported_smooth_and_surgery_model_package_of_homeomorph_to_onePoint_threeSpace
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
A concrete sphere-recognition homeomorphism selects the one-point
compactification route used by smoothability, the exact transported charted
space from that route, the `C∞` and surgery-model manifold witnesses, and the
topological prerequisites needed by the Ricci-flow-with-surgery layer.
-/
theorem smoothability_selected_threeSphere_homeomorph_transported_package
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ ThreeSphere) :
    ∃ modelHomeomorph :
      OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere,
    ∃ onePointHomeomorph :
      M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)),
    ∃ charted : ChartedSpace ThreeManifoldModel M,
      onePointHomeomorph = e.trans modelHomeomorph.symm ∧
        charted =
          homeomorphToOnePoint_threeSpace_smoothChartedSpace
            onePointHomeomorph ∧
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold (𝓡 3) ∞ M) ∧
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        ∃ _t2 : T2Space M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
          Nonempty M := by
  rcases onePoint_threeSpace_homeomorph_threeSphere with ⟨modelHomeomorph⟩
  let onePointHomeomorph :
      M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)) :=
    e.trans modelHomeomorph.symm
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace onePointHomeomorph
  have smooth :
      letI : ChartedSpace ThreeManifoldModel M := charted
      IsManifold (𝓡 3) ∞ M := by
    exact homeomorphToOnePoint_threeSpace_smoothManifold onePointHomeomorph
  have surgeryModel :
      letI : ChartedSpace ThreeManifoldModel M := charted
      IsManifold ThreeManifoldModelWithCorners 1 M := by
    exact
      homeomorphToOnePoint_threeSpace_surgeryModel_isManifold
        onePointHomeomorph
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      ⟨onePointHomeomorph⟩ with
    ⟨t2, _charted, simple, compact, _smooth, nonempty⟩
  exact
    ⟨ modelHomeomorph
    , onePointHomeomorph
    , charted
    , rfl
    , rfl
    , smooth
    , surgeryModel
    , t2
    , simple
    , compact
    , nonempty
    ⟩

/--
Sphere recognition closes the same transported smoothability bridge by
converting the recognized sphere to the one-point compactification model.
-/
theorem smoothabilityTransportedBridgeStatement_of_threeSphereRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) →
          ∃ charted : ChartedSpace ThreeManifoldModel M,
            letI : ChartedSpace ThreeManifoldModel M := charted
            IsManifold ThreeManifoldModelWithCorners 1 M := by
  intro M _top _t2 _simple _compact h
  exact
    smoothabilityTransportedBridgeStatement_of_onePointRecognition M
      (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
Sphere recognition similarly closes the transported `C∞` smooth-manifold
statement through the one-point compactification equivalence.
-/
theorem smoothabilityTransportedSmoothManifoldStatement_of_threeSphereRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) →
          ∃ charted : ChartedSpace ThreeManifoldModel M,
            letI : ChartedSpace ThreeManifoldModel M := charted
            IsManifold (𝓡 3) ∞ M := by
  intro M _top _t2 _simple _compact h
  exact
    smoothabilityTransportedSmoothManifoldStatement_of_onePointRecognition M
      (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere h)

/--
Recognition as `ThreeSphere` directly supplies the smooth structure needed by
the surgery model: a transported `ThreeManifoldModel` charted space together
with the corresponding `C¹` manifold witness.
-/
theorem smoothability_surgery_model_smooth_structure_of_homeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
      IsManifold ThreeManifoldModelWithCorners 1 M := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_threeSphere h with
    ⟨_t2, charted, _simple, _compact, smooth, _nonempty⟩
  exact ⟨charted, smooth⟩

/--
A target-family `ThreeSphere` recognition theorem therefore gives a
target-family supply of surgery-model smooth structures.  This is the
smoothability-side family payload expected after topology recognition has
collapsed each target to `ThreeSphere`.
-/
theorem smoothability_surgery_model_smooth_structure_family_of_homeomorph_to_threeSphere
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    ∀ (M : Type u) [TopologicalSpace M],
      ∃ _charted : ChartedSpace ThreeManifoldModel M,
        IsManifold ThreeManifoldModelWithCorners 1 M := by
  intro M _top
  exact
    smoothability_surgery_model_smooth_structure_of_homeomorph_to_threeSphere
      (recognize M)

/--
A target-family one-point recognition theorem supplies the synchronized
transported smoothability package for every target: the selected transported
charted space, the `C∞` smooth-manifold proof, the `C¹` surgery-model proof,
and the topological prerequisites all come from the same recognition route.
-/
theorem smoothability_transported_smooth_and_surgery_model_package_family_of_onePointRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M],
        Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∀ (M : Type u) [TopologicalSpace M],
      ∃ charted : ChartedSpace ThreeManifoldModel M,
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold (𝓡 3) ∞ M) ∧
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        ∃ _t2 : T2Space M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
          Nonempty M := by
  intro M _top
  exact
    smoothability_transported_smooth_and_surgery_model_package_of_homeomorph_to_onePoint_threeSpace
      (recognize M)

/--
A target-family `ThreeSphere` recognition theorem gives the same synchronized
transported smoothability package after converting each recognized target to
the one-point compactification model.
-/
theorem smoothability_transported_smooth_and_surgery_model_package_family_of_threeSphereRecognition
    (recognize :
      ∀ (M : Type u) [TopologicalSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    ∀ (M : Type u) [TopologicalSpace M],
      ∃ charted : ChartedSpace ThreeManifoldModel M,
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold (𝓡 3) ∞ M) ∧
        (letI : ChartedSpace ThreeManifoldModel M := charted
         IsManifold ThreeManifoldModelWithCorners 1 M) ∧
        ∃ _t2 : T2Space M,
        ∃ _simple : SimplyConnectedSpace M,
        ∃ _compact : CompactSpace M,
          Nonempty M := by
  intro M _top
  exact
    smoothability_transported_smooth_and_surgery_model_package_of_homeomorph_to_threeSphere
      (recognize M)

end Poincare
