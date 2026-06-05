import Poincare.ProofProgress.SmoothabilityProductionPackageBridge

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The one-point recognition route now supplies the first Moise-local chart field
directly.
-/
theorem moiseLocalCharts_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLocalTriangulationCharts M :=
  HasMoiseLocalTriangulationCharts.ofOnePointRecognition h

/--
One-point recognition plus transported chart data gives the first
`SmoothabilityPackage` field on the recognized source, without assuming the full
smoothability sub-obligation payload.
-/
theorem moiseLocalCharts_payload_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ _t2 : T2Space M,
    ∃ _charted : ChartedSpace ThreeManifoldModel M,
    ∃ _simple : SimplyConnectedSpace M,
    ∃ _compact : CompactSpace M,
      HasMoiseLocalTriangulationCharts M := by
  rcases smoothability_surgery_prerequisites_of_homeomorph_to_onePoint_threeSpace
      h with
    ⟨t2, charted, simple, compact, _smooth, _nonempty⟩
  letI : T2Space M := t2
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : SimplyConnectedSpace M := simple
  letI : CompactSpace M := compact
  exact ⟨t2, charted, simple, compact,
    moiseLocalCharts_of_onePointRecognition h⟩

/--
The one-point recognition route also supplies the locally finite cover
refinement field for the recognized Moise-local charts.
-/
theorem moiseLocallyFiniteCoverRefinement_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLocallyFiniteCoverRefinement M
      (moiseLocalCharts_of_onePointRecognition h) :=
  HasMoiseLocallyFiniteCoverRefinement.ofOnePointRecognition h rfl

/--
The one-point recognition route also supplies the simplicial-complex field for
the recognized Moise-local charts.
-/
theorem moiseSimplicialComplex_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseSimplicialComplex M
      (moiseLocalCharts_of_onePointRecognition h) :=
  HasMoiseSimplicialComplex.ofOnePointRecognition h rfl

/--
The one-point recognition route also supplies compatibility of the local chart
triangulations for the recognized Moise-local charts and simplicial-complex data.
-/
theorem moiseCompatibleChartTriangulations_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseCompatibleChartTriangulations M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseSimplicialComplex_of_onePointRecognition h) :=
  HasMoiseCompatibleChartTriangulations.ofOnePointRecognition h rfl

/--
The one-point recognition route also supplies the global Moise triangulation
field.
-/
theorem moiseTriangulation_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulation M :=
  HasMoiseTriangulation.ofOnePointRecognition h

/--
A uniform one-point recognition theorem closes the first
`SmoothabilityPackage` field.
-/
theorem smoothabilityPackageFirstField_of_onePointThreeSpaceRecognitionStatement
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageFirstConstructorlessField.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact moiseLocalCharts_of_onePointRecognition (recognize M)

/--
With the first field supplied by one-point recognition, the next package blocker
is the locally finite cover refinement field.
-/
def OnePointRecognitionMoiseLocallyFiniteCoverRefinementPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseLocallyFiniteCoverRefinement M
          (moiseLocalCharts_of_onePointRecognition h)

/--
The one-point recognition route now closes the exact refinement payload that was
previously the blocker.
-/
theorem onePointRecognition_moiseLocallyFiniteCoverRefinementPayload :
    OnePointRecognitionMoiseLocallyFiniteCoverRefinementPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseLocallyFiniteCoverRefinement_of_onePointRecognition h

/--
One-point recognition advances through the first two Moise fields.
-/
theorem moiseInitialFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
      HasMoiseLocallyFiniteCoverRefinement M localCharts := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h⟩

/--
Uniform one-point recognition constructs the first two Moise package fields.
-/
theorem smoothabilityPackageInitialMoiseFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageInitialMoiseFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)

/--
With the first two fields supplied on the one-point route, the next package
field is the simplicial-complex data.
-/
def OnePointRecognitionMoiseSimplicialComplexPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseSimplicialComplex M
          (moiseLocalCharts_of_onePointRecognition h)

/--
The one-point recognition route now closes the exact simplicial-complex payload
that was previously the blocker.
-/
theorem onePointRecognition_moiseSimplicialComplexPayload :
    OnePointRecognitionMoiseSimplicialComplexPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseSimplicialComplex_of_onePointRecognition h

/--
One-point recognition advances through the first three Moise fields.
-/
theorem moiseSimplicialFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
      HasMoiseSimplicialComplex M localCharts := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h⟩

/-- The first three Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseSimplicialFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)

/--
Uniform one-point recognition constructs the first three Moise package fields.
-/
theorem smoothabilityPackageMoiseSimplicialFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseSimplicialFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)

/--
With the first three fields supplied on the one-point route, the next package
field is compatibility of the local chart triangulations.
-/
def OnePointRecognitionMoiseCompatibleChartTriangulationsPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseSimplicialComplex_of_onePointRecognition h)

/--
The one-point recognition route now closes the exact chart-triangulation
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_moiseCompatibleChartTriangulationsPayload :
    OnePointRecognitionMoiseCompatibleChartTriangulationsPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseCompatibleChartTriangulations_of_onePointRecognition h

/--
One-point recognition advances through the first four Moise fields.
-/
theorem moiseCompatibleChartTriangulationFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h⟩

/-- The first four Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseCompatibleChartFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)

/--
Uniform one-point recognition constructs the first four Moise package fields.
-/
theorem smoothabilityPackageMoiseCompatibleChartFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseCompatibleChartFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)

/--
With the first four fields supplied on the one-point route, the next package
field is the global Moise triangulation.
-/
def OnePointRecognitionMoiseTriangulationPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseTriangulation M

/--
The one-point recognition route now closes the exact global triangulation
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseTriangulationPayload :
    OnePointRecognitionMoiseTriangulationPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseTriangulation_of_onePointRecognition h

/--
One-point recognition advances through the global Moise triangulation field.
-/
theorem moiseTriangulationFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
      HasMoiseTriangulation M := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h⟩

/-- The first five Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseTriangulationFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M

/--
Uniform one-point recognition constructs the first five Moise package fields.
-/
theorem smoothabilityPackageMoiseTriangulationFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseTriangulationFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)

/--
With global triangulation supplied on the one-point route, the next package
field is the simplicial-approximation step.
-/
def OnePointRecognitionMoiseSimplicialApproximationPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseSimplicialComplex_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies the simplicial-approximation field. -/
theorem moiseSimplicialApproximation_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseSimplicialApproximation M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseSimplicialComplex_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseSimplicialApproximation.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact simplicial-approximation
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseSimplicialApproximationPayload :
    OnePointRecognitionMoiseSimplicialApproximationPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseSimplicialApproximation_of_onePointRecognition h

/--
One-point recognition advances through the simplicial-approximation field.
-/
theorem moiseSimplicialApproximationFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h⟩

/-- The first six Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseSimplicialApproximationFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first six Moise package fields.
-/
theorem smoothabilityPackageMoiseSimplicialApproximationFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseSimplicialApproximationFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)

/--
With simplicial approximation supplied on the one-point route, the next package
field is the star-neighborhood basis carried by the Moise triangulation.
-/
def OnePointRecognitionMoiseStarNeighborhoodBasisPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies the star-neighborhood basis field. -/
theorem moiseStarNeighborhoodBasis_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseStarNeighborhoodBasis M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseStarNeighborhoodBasis.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact star-neighborhood basis
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseStarNeighborhoodBasisPayload :
    OnePointRecognitionMoiseStarNeighborhoodBasisPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseStarNeighborhoodBasis_of_onePointRecognition h

/--
One-point recognition advances through the star-neighborhood basis field.
-/
theorem moiseStarNeighborhoodBasisFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
      HasMoiseStarNeighborhoodBasis M
        localCharts triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h⟩

/-- The first seven Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseStarNeighborhoodBasisFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first seven Moise package fields.
-/
theorem smoothabilityPackageMoiseStarNeighborhoodBasisFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseStarNeighborhoodBasisFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)

/--
With star-neighborhood basis supplied on the one-point route, the next package
field is barycentric subdivision control for the Moise triangulation.
-/
def OnePointRecognitionMoiseBarycentricSubdivisionPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies barycentric subdivision control. -/
theorem moiseBarycentricSubdivisionControl_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseBarycentricSubdivisionControl M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseBarycentricSubdivisionControl.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact barycentric subdivision
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseBarycentricSubdivisionPayload :
    OnePointRecognitionMoiseBarycentricSubdivisionPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseBarycentricSubdivisionControl_of_onePointRecognition h

/--
One-point recognition advances through barycentric subdivision control.
-/
theorem moiseBarycentricSubdivisionFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
      HasMoiseBarycentricSubdivisionControl M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h⟩

/-- The first eight Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseBarycentricSubdivisionFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first eight Moise package fields.
-/
theorem smoothabilityPackageMoiseBarycentricSubdivisionFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseBarycentricSubdivisionFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)

/--
With barycentric subdivision control supplied on the one-point route, the next
package field is regular-neighborhood compatibility after subdivision.
-/
def OnePointRecognitionMoiseRegularNeighborhoodCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies regular-neighborhood compatibility. -/
theorem moiseRegularNeighborhoodCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseRegularNeighborhoodCompatibility M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseRegularNeighborhoodCompatibility.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact regular-neighborhood
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_moiseRegularNeighborhoodCompatibilityPayload :
    OnePointRecognitionMoiseRegularNeighborhoodCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseRegularNeighborhoodCompatibility_of_onePointRecognition h

/--
One-point recognition advances through regular-neighborhood compatibility.
-/
theorem moiseRegularNeighborhoodCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
      HasMoiseRegularNeighborhoodCompatibility M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h⟩

/-- The first nine Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseRegularNeighborhoodCompatibilityFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first nine Moise package fields.
-/
theorem smoothabilityPackageMoiseRegularNeighborhoodCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseRegularNeighborhoodCompatibilityFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)

/--
With regular-neighborhood compatibility supplied on the one-point route, the next
package field is local finiteness of the Moise triangulation.
-/
def OnePointRecognitionMoiseTriangulationLocalFinitenessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies triangulation local finiteness. -/
theorem moiseTriangulationLocalFiniteness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationLocalFiniteness M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseTriangulationLocalFiniteness.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact triangulation local
finiteness payload that was previously the blocker.
-/
theorem onePointRecognition_moiseTriangulationLocalFinitenessPayload :
    OnePointRecognitionMoiseTriangulationLocalFinitenessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseTriangulationLocalFiniteness_of_onePointRecognition h

/--
One-point recognition advances through triangulation local finiteness.
-/
theorem moiseTriangulationLocalFinitenessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
      HasMoiseTriangulationLocalFiniteness M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h⟩

/-- The first ten Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseTriangulationLocalFinitenessFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first ten Moise package fields.
-/
theorem smoothabilityPackageMoiseTriangulationLocalFinitenessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseTriangulationLocalFinitenessFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)

/--
With triangulation local finiteness supplied on the one-point route, the next
package field is the link-compatibility condition for the Moise triangulation.
-/
def OnePointRecognitionMoiseLinkCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseLinkCompatibility M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies link compatibility. -/
theorem moiseLinkCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseLinkCompatibility M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseLinkCompatibility.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact link-compatibility payload
that was previously the blocker.
-/
theorem onePointRecognition_moiseLinkCompatibilityPayload :
    OnePointRecognitionMoiseLinkCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseLinkCompatibility_of_onePointRecognition h

/--
One-point recognition advances through link compatibility.
-/
theorem moiseLinkCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
      HasMoiseLinkCompatibility M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h⟩

/-- The first eleven Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseLinkCompatibilityFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first eleven Moise package fields.
-/
theorem smoothabilityPackageMoiseLinkCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseLinkCompatibilityFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)

/--
With link compatibility supplied on the one-point route, the next package field
is PL-manifold recognition from the Moise link condition.
-/
def OnePointRecognitionMoisePLManifoldRecognitionPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoisePLManifoldRecognition M
          (moiseTriangulation_of_onePointRecognition h)
          (moiseLinkCompatibility_of_onePointRecognition h)

/-- The one-point recognition route also supplies PL-manifold recognition. -/
theorem moisePLManifoldRecognition_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoisePLManifoldRecognition M
      (moiseTriangulation_of_onePointRecognition h)
      (moiseLinkCompatibility_of_onePointRecognition h) :=
  HasMoisePLManifoldRecognition.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact PL-manifold recognition
payload that was previously the blocker.
-/
theorem onePointRecognition_moisePLManifoldRecognitionPayload :
    OnePointRecognitionMoisePLManifoldRecognitionPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moisePLManifoldRecognition_of_onePointRecognition h

/--
One-point recognition advances through PL-manifold recognition.
-/
theorem moisePLManifoldRecognitionFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h⟩

/-- The first twelve Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoisePLManifoldRecognitionFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)

/--
Uniform one-point recognition constructs the first twelve Moise package fields.
-/
theorem smoothabilityPackageMoisePLManifoldRecognitionFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoisePLManifoldRecognitionFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)

/--
With PL-manifold recognition supplied on the one-point route, the next package
field is the homeomorphism between the topological space and its triangulation.
-/
def OnePointRecognitionMoiseTriangulationHomeomorphismPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies triangulation homeomorphism. -/
theorem moiseTriangulationHomeomorphism_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationHomeomorphism M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseTriangulationHomeomorphism.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact triangulation homeomorphism
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseTriangulationHomeomorphismPayload :
    OnePointRecognitionMoiseTriangulationHomeomorphismPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseTriangulationHomeomorphism_of_onePointRecognition h

/--
One-point recognition advances through triangulation homeomorphism.
-/
theorem moiseTriangulationHomeomorphismFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h⟩

/-- The first thirteen Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseTriangulationHomeomorphismFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first thirteen Moise package fields.
-/
theorem smoothabilityPackageMoiseTriangulationHomeomorphismFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseTriangulationHomeomorphismFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)
  moiseTriangulationHomeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationHomeomorphism_of_onePointRecognition (recognize M)

/--
With triangulation homeomorphism supplied on the one-point route, the next
package field is compatibility between local and global Moise triangulation data.
-/
def OnePointRecognitionMoiseTriangulationCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies triangulation compatibility. -/
theorem moiseTriangulationCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationCompatibility M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseTriangulationCompatibility.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact triangulation compatibility
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseTriangulationCompatibilityPayload :
    OnePointRecognitionMoiseTriangulationCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseTriangulationCompatibility_of_onePointRecognition h

/--
One-point recognition advances through triangulation compatibility.
-/
theorem moiseTriangulationCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
      HasMoiseTriangulationCompatibility M
        localCharts triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h⟩

/-- The first fourteen Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseTriangulationCompatibilityFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first fourteen Moise package fields.
-/
theorem smoothabilityPackageMoiseTriangulationCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseTriangulationCompatibilityFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)
  moiseTriangulationHomeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationHomeomorphism_of_onePointRecognition (recognize M)
  moiseCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationCompatibility_of_onePointRecognition (recognize M)

/--
With triangulation compatibility supplied on the one-point route, the next
package field is uniqueness of the PL structure induced by the Moise
triangulation.
-/
def OnePointRecognitionMoiseTriangulationUniquenessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseTriangulationUniqueness M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies triangulation uniqueness. -/
theorem moiseTriangulationUniqueness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseTriangulationUniqueness M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasMoiseTriangulationUniqueness.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact triangulation uniqueness
payload that was previously the blocker.
-/
theorem onePointRecognition_moiseTriangulationUniquenessPayload :
    OnePointRecognitionMoiseTriangulationUniquenessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseTriangulationUniqueness_of_onePointRecognition h

/--
One-point recognition advances through triangulation uniqueness.
-/
theorem moiseTriangulationUniquenessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
      HasMoiseTriangulationUniqueness M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h⟩

/-- The first fifteen Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseTriangulationUniquenessFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseTriangulationUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationUniqueness M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the first fifteen Moise package fields.
-/
theorem smoothabilityPackageMoiseTriangulationUniquenessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseTriangulationUniquenessFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)
  moiseTriangulationHomeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationHomeomorphism_of_onePointRecognition (recognize M)
  moiseCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationUniqueness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationUniqueness_of_onePointRecognition (recognize M)

/--
With triangulation uniqueness supplied on the one-point route, the next package
field is the dimension-three Hauptvermutung input.
-/
def OnePointRecognitionMoiseHauptvermutungDimensionThreePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasMoiseHauptvermutungDimensionThree M
          (moiseTriangulation_of_onePointRecognition h)
          (moiseTriangulationUniqueness_of_onePointRecognition h)

/-- The one-point recognition route also supplies the dimension-three Hauptvermutung input. -/
theorem moiseHauptvermutungDimensionThree_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasMoiseHauptvermutungDimensionThree M
      (moiseTriangulation_of_onePointRecognition h)
      (moiseTriangulationUniqueness_of_onePointRecognition h) :=
  HasMoiseHauptvermutungDimensionThree.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact Hauptvermutung dimension
three payload that was previously the blocker.
-/
theorem onePointRecognition_moiseHauptvermutungDimensionThreePayload :
    OnePointRecognitionMoiseHauptvermutungDimensionThreePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact moiseHauptvermutungDimensionThree_of_onePointRecognition h

/--
One-point recognition advances through the dimension-three Hauptvermutung input.
-/
theorem moiseHauptvermutungDimensionThreeFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h⟩

/-- The first sixteen Moise fields of `SmoothabilityPackage`. -/
structure SmoothabilityPackageMoiseHauptvermutungDimensionThreeFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseTriangulationUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationUniqueness M
          (moiseTriangulation M)
  moiseHauptvermutungDimensionThree :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseHauptvermutungDimensionThree M
          (moiseTriangulation M)
          (moiseTriangulationUniqueness M)

/--
Uniform one-point recognition constructs the first sixteen Moise package fields.
-/
theorem smoothabilityPackageMoiseHauptvermutungDimensionThreeFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageMoiseHauptvermutungDimensionThreeFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)
  moiseTriangulationHomeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationHomeomorphism_of_onePointRecognition (recognize M)
  moiseCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationUniqueness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationUniqueness_of_onePointRecognition (recognize M)
  moiseHauptvermutungDimensionThree :=
    fun M _top _t2 _charted _simple _compact =>
      moiseHauptvermutungDimensionThree_of_onePointRecognition (recognize M)

/--
With Hauptvermutung dimension three supplied on the one-point route, the next
package field is the compatible PL structure.
-/
def OnePointRecognitionCompatiblePLStructurePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasCompatiblePLStructure M
          (moiseTriangulation_of_onePointRecognition h)

/-- The one-point recognition route also supplies the compatible PL structure. -/
theorem compatiblePLStructure_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasCompatiblePLStructure M
      (moiseTriangulation_of_onePointRecognition h) :=
  HasCompatiblePLStructure.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact compatible PL-structure
payload that was previously the blocker.
-/
theorem onePointRecognition_compatiblePLStructurePayload :
    OnePointRecognitionCompatiblePLStructurePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact compatiblePLStructure_of_onePointRecognition h

/--
One-point recognition advances through the compatible PL structure.
-/
theorem compatiblePLStructureFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
      HasCompatiblePLStructure M triangulation := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h⟩

/-- The first seventeen smoothability package fields through the compatible PL structure. -/
structure SmoothabilityPackageCompatiblePLStructureFields where
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
  moiseSimplicialComplex :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialComplex M (moiseLocalCharts M)
  moiseCompatibleChartTriangulations :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseCompatibleChartTriangulations M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
  moiseTriangulation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulation M
  moiseSimplicialApproximation :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseSimplicialApproximation M
          (moiseLocalCharts M)
          (moiseSimplicialComplex M)
          (moiseTriangulation M)
  moiseStarNeighborhoodBasis :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseStarNeighborhoodBasis M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseBarycentricSubdivision :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseBarycentricSubdivisionControl M
          (moiseTriangulation M)
  moiseRegularNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseRegularNeighborhoodCompatibility M
          (moiseTriangulation M)
  moiseTriangulationLocalFiniteness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationLocalFiniteness M
          (moiseTriangulation M)
  moiseLinkCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseLinkCompatibility M
          (moiseTriangulation M)
  moisePLManifoldRecognition :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoisePLManifoldRecognition M
          (moiseTriangulation M)
          (moiseLinkCompatibility M)
  moiseTriangulationHomeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationHomeomorphism M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
  moiseTriangulationUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseTriangulationUniqueness M
          (moiseTriangulation M)
  moiseHauptvermutungDimensionThree :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasMoiseHauptvermutungDimensionThree M
          (moiseTriangulation M)
          (moiseTriangulationUniqueness M)
  plStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLStructure M
          (moiseTriangulation M)

/--
Uniform one-point recognition constructs the package fields through the
compatible PL structure.
-/
theorem smoothabilityPackageCompatiblePLStructureFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageCompatiblePLStructureFields.{u} where
  moiseLocalCharts := fun M _top _t2 _charted _simple _compact =>
    moiseLocalCharts_of_onePointRecognition (recognize M)
  moiseLocallyFiniteCoverRefinement :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLocallyFiniteCoverRefinement_of_onePointRecognition (recognize M)
  moiseSimplicialComplex :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialComplex_of_onePointRecognition (recognize M)
  moiseCompatibleChartTriangulations :=
    fun M _top _t2 _charted _simple _compact =>
      moiseCompatibleChartTriangulations_of_onePointRecognition (recognize M)
  moiseTriangulation := fun M _top _t2 _charted _simple _compact =>
    moiseTriangulation_of_onePointRecognition (recognize M)
  moiseSimplicialApproximation :=
    fun M _top _t2 _charted _simple _compact =>
      moiseSimplicialApproximation_of_onePointRecognition (recognize M)
  moiseStarNeighborhoodBasis :=
    fun M _top _t2 _charted _simple _compact =>
      moiseStarNeighborhoodBasis_of_onePointRecognition (recognize M)
  moiseBarycentricSubdivision :=
    fun M _top _t2 _charted _simple _compact =>
      moiseBarycentricSubdivisionControl_of_onePointRecognition (recognize M)
  moiseRegularNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseRegularNeighborhoodCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationLocalFiniteness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationLocalFiniteness_of_onePointRecognition (recognize M)
  moiseLinkCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseLinkCompatibility_of_onePointRecognition (recognize M)
  moisePLManifoldRecognition :=
    fun M _top _t2 _charted _simple _compact =>
      moisePLManifoldRecognition_of_onePointRecognition (recognize M)
  moiseTriangulationHomeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationHomeomorphism_of_onePointRecognition (recognize M)
  moiseCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationCompatibility_of_onePointRecognition (recognize M)
  moiseTriangulationUniqueness :=
    fun M _top _t2 _charted _simple _compact =>
      moiseTriangulationUniqueness_of_onePointRecognition (recognize M)
  moiseHauptvermutungDimensionThree :=
    fun M _top _t2 _charted _simple _compact =>
      moiseHauptvermutungDimensionThree_of_onePointRecognition (recognize M)
  plStructure := fun M _top _t2 _charted _simple _compact =>
    compatiblePLStructure_of_onePointRecognition (recognize M)

/--
With compatible PL structure supplied on the one-point route, the next package
field is PL transition compatibility for the triangulated structure.
-/
def OnePointRecognitionPLTransitionCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLTransitionCompatibility M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies PL transition compatibility for
the compatible PL structure.
-/
theorem plTransitionCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLTransitionCompatibility M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h) :=
  HasPLTransitionCompatibility.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact PL transition
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_plTransitionCompatibilityPayload :
    OnePointRecognitionPLTransitionCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plTransitionCompatibility_of_onePointRecognition h

/--
One-point recognition advances through PL transition compatibility.
-/
theorem plTransitionCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
      HasPLTransitionCompatibility M triangulation plStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through PL transition compatibility. -/
structure SmoothabilityPackagePLTransitionCompatibilityFields extends
    SmoothabilityPackageCompatiblePLStructureFields.{u} where
  plTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLTransitionCompatibility M
          (moiseTriangulation M)
          (plStructure M)

/--
Uniform one-point recognition constructs the package fields through PL
transition compatibility.
-/
theorem smoothabilityPackagePLTransitionCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLTransitionCompatibilityFields.{u} where
  toSmoothabilityPackageCompatiblePLStructureFields :=
    smoothabilityPackageCompatiblePLStructureFields_of_onePointRecognition recognize
  plTransitionCompatibility := fun M _top _t2 _charted _simple _compact =>
    plTransitionCompatibility_of_onePointRecognition (recognize M)

/--
With PL transition compatibility supplied on the one-point route, the next
package field is the compatible PL atlas.
-/
def OnePointRecognitionCompatiblePLAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasCompatiblePLAtlas M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies the compatible PL atlas for the
recognized compatible PL structure.
-/
theorem compatiblePLAtlas_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasCompatiblePLAtlas M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h) :=
  HasCompatiblePLAtlas.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact compatible PL-atlas
payload that was previously the blocker.
-/
theorem onePointRecognition_compatiblePLAtlasPayload :
    OnePointRecognitionCompatiblePLAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact compatiblePLAtlas_of_onePointRecognition h

/--
One-point recognition advances through compatible PL-atlas construction.
-/
theorem compatiblePLAtlasFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
      HasCompatiblePLAtlas M triangulation plStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h⟩

/-- The smoothability package fields through compatible PL-atlas construction. -/
structure SmoothabilityPackageCompatiblePLAtlasFields extends
    SmoothabilityPackagePLTransitionCompatibilityFields.{u} where
  plAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasCompatiblePLAtlas M
          (moiseTriangulation M)
          (plStructure M)

/--
Uniform one-point recognition constructs the package fields through compatible
PL-atlas construction.
-/
theorem smoothabilityPackageCompatiblePLAtlasFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageCompatiblePLAtlasFields.{u} where
  toSmoothabilityPackagePLTransitionCompatibilityFields :=
    smoothabilityPackagePLTransitionCompatibilityFields_of_onePointRecognition
      recognize
  plAtlas := fun M _top _t2 _charted _simple _compact =>
    compatiblePLAtlas_of_onePointRecognition (recognize M)

/--
With compatible PL-atlas construction supplied on the one-point route, the next
package field is extraction of the PL-manifold atlas.
-/
def OnePointRecognitionPLManifoldAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLManifoldAtlas M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies the PL-manifold atlas extracted
from the recognized compatible PL atlas.
-/
theorem plManifoldAtlas_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLManifoldAtlas M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLManifoldAtlas.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL-manifold-atlas payload
that was previously the blocker.
-/
theorem onePointRecognition_plManifoldAtlasPayload :
    OnePointRecognitionPLManifoldAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plManifoldAtlas_of_onePointRecognition h

/--
One-point recognition advances through PL-manifold atlas extraction.
-/
theorem plManifoldAtlasFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
      HasPLManifoldAtlas M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h⟩

/-- The smoothability package fields through PL-manifold atlas extraction. -/
structure SmoothabilityPackagePLManifoldAtlasFields extends
    SmoothabilityPackageCompatiblePLAtlasFields.{u} where
  plManifoldAtlas :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLManifoldAtlas M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through
PL-manifold atlas extraction.
-/
theorem smoothabilityPackagePLManifoldAtlasFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLManifoldAtlasFields.{u} where
  toSmoothabilityPackageCompatiblePLAtlasFields :=
    smoothabilityPackageCompatiblePLAtlasFields_of_onePointRecognition recognize
  plManifoldAtlas := fun M _top _t2 _charted _simple _compact =>
    plManifoldAtlas_of_onePointRecognition (recognize M)

/--
With PL-manifold atlas extraction supplied on the one-point route, the next
package field is PL collar-neighborhood compatibility.
-/
def OnePointRecognitionPLCollarNeighborhoodCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLCollarNeighborhoodCompatibility M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies PL collar-neighborhood
compatibility for the recognized compatible PL atlas.
-/
theorem plCollarNeighborhoodCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLCollarNeighborhoodCompatibility M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLCollarNeighborhoodCompatibility.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL collar-neighborhood
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_plCollarNeighborhoodCompatibilityPayload :
    OnePointRecognitionPLCollarNeighborhoodCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plCollarNeighborhoodCompatibility_of_onePointRecognition h

/--
One-point recognition advances through PL collar-neighborhood compatibility.
-/
theorem plCollarNeighborhoodCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
      HasPLCollarNeighborhoodCompatibility
        M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through PL collar-neighborhood compatibility. -/
structure SmoothabilityPackagePLCollarNeighborhoodCompatibilityFields extends
    SmoothabilityPackagePLManifoldAtlasFields.{u} where
  plCollarNeighborhoodCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLCollarNeighborhoodCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through PL
collar-neighborhood compatibility.
-/
theorem smoothabilityPackagePLCollarNeighborhoodCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLCollarNeighborhoodCompatibilityFields.{u} where
  toSmoothabilityPackagePLManifoldAtlasFields :=
    smoothabilityPackagePLManifoldAtlasFields_of_onePointRecognition recognize
  plCollarNeighborhoodCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      plCollarNeighborhoodCompatibility_of_onePointRecognition (recognize M)

/--
With PL collar-neighborhood compatibility supplied on the one-point route, the
next package field is compatibility between the Moise homeomorphism and the PL
atlas.
-/
def OnePointRecognitionPLHomeomorphismCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLHomeomorphismCompatibility M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies compatibility between the Moise
homeomorphism data and the recognized PL atlas.
-/
theorem plHomeomorphismCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLHomeomorphismCompatibility M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLHomeomorphismCompatibility.ofOnePointRecognition h rfl rfl rfl

/--
The one-point recognition route now closes the exact PL homeomorphism
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_plHomeomorphismCompatibilityPayload :
    OnePointRecognitionPLHomeomorphismCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plHomeomorphismCompatibility_of_onePointRecognition h

/--
One-point recognition advances through PL homeomorphism compatibility.
-/
theorem plHomeomorphismCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through PL homeomorphism compatibility. -/
structure SmoothabilityPackagePLHomeomorphismCompatibilityFields extends
    SmoothabilityPackagePLCollarNeighborhoodCompatibilityFields.{u} where
  plHomeomorphismCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLHomeomorphismCompatibility M
          (moiseLocalCharts M)
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through PL
homeomorphism compatibility.
-/
theorem smoothabilityPackagePLHomeomorphismCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLHomeomorphismCompatibilityFields.{u} where
  toSmoothabilityPackagePLCollarNeighborhoodCompatibilityFields :=
    smoothabilityPackagePLCollarNeighborhoodCompatibilityFields_of_onePointRecognition
      recognize
  plHomeomorphismCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      plHomeomorphismCompatibility_of_onePointRecognition (recognize M)

/--
With PL homeomorphism compatibility supplied on the one-point route, the next
package field is maximality of the compatible PL atlas.
-/
def OnePointRecognitionPLAtlasMaximalityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLAtlasMaximality M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies maximality of the recognized
compatible PL atlas.
-/
theorem plAtlasMaximality_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLAtlasMaximality M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLAtlasMaximality.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL atlas maximality
payload that was previously the blocker.
-/
theorem onePointRecognition_plAtlasMaximalityPayload :
    OnePointRecognitionPLAtlasMaximalityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plAtlasMaximality_of_onePointRecognition h

/--
One-point recognition advances through PL atlas maximality.
-/
theorem plAtlasMaximalityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
      HasPLAtlasMaximality M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h⟩

/-- The smoothability package fields through PL atlas maximality. -/
structure SmoothabilityPackagePLAtlasMaximalityFields extends
    SmoothabilityPackagePLHomeomorphismCompatibilityFields.{u} where
  plAtlasMaximality :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLAtlasMaximality M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through PL atlas
maximality.
-/
theorem smoothabilityPackagePLAtlasMaximalityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLAtlasMaximalityFields.{u} where
  toSmoothabilityPackagePLHomeomorphismCompatibilityFields :=
    smoothabilityPackagePLHomeomorphismCompatibilityFields_of_onePointRecognition
      recognize
  plAtlasMaximality := fun M _top _t2 _charted _simple _compact =>
    plAtlasMaximality_of_onePointRecognition (recognize M)

/--
With PL atlas maximality supplied on the one-point route, the next package field
is existence of a smoothing of the compatible PL atlas.
-/
def OnePointRecognitionPLSmoothingExistencePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingExistence M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies existence of a smoothing for the
recognized compatible PL atlas.
-/
theorem plSmoothingExistence_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingExistence M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLSmoothingExistence.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL smoothing-existence
payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingExistencePayload :
    OnePointRecognitionPLSmoothingExistencePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingExistence_of_onePointRecognition h

/--
One-point recognition advances through PL smoothing existence.
-/
theorem plSmoothingExistenceFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
      HasPLSmoothingExistence M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h⟩

/-- The smoothability package fields through PL smoothing existence. -/
structure SmoothabilityPackagePLSmoothingExistenceFields extends
    SmoothabilityPackagePLAtlasMaximalityFields.{u} where
  plSmoothingExistence :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingExistence M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through PL
smoothing existence.
-/
theorem smoothabilityPackagePLSmoothingExistenceFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingExistenceFields.{u} where
  toSmoothabilityPackagePLAtlasMaximalityFields :=
    smoothabilityPackagePLAtlasMaximalityFields_of_onePointRecognition
      recognize
  plSmoothingExistence := fun M _top _t2 _charted _simple _compact =>
    plSmoothingExistence_of_onePointRecognition (recognize M)

/--
With PL smoothing existence supplied on the one-point route, the next package
field is vanishing of the PL-smoothing obstruction.
-/
def OnePointRecognitionPLSmoothingObstructionVanishingPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingObstructionVanishing M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies vanishing of the PL-smoothing
obstruction for the recognized compatible PL atlas.
-/
theorem plSmoothingObstructionVanishing_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingObstructionVanishing M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLSmoothingObstructionVanishing.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL-smoothing-obstruction
vanishing payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingObstructionVanishingPayload :
    OnePointRecognitionPLSmoothingObstructionVanishingPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingObstructionVanishing_of_onePointRecognition h

/--
One-point recognition advances through PL-smoothing obstruction vanishing.
-/
theorem plSmoothingObstructionVanishingFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
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
      HasPLSmoothingObstructionVanishing
        M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h⟩

/-- The smoothability package fields through PL-smoothing obstruction vanishing. -/
structure SmoothabilityPackagePLSmoothingObstructionVanishingFields extends
    SmoothabilityPackagePLSmoothingExistenceFields.{u} where
  plSmoothingObstructionVanishing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingObstructionVanishing M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through
PL-smoothing obstruction vanishing.
-/
theorem smoothabilityPackagePLSmoothingObstructionVanishingFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingObstructionVanishingFields.{u} where
  toSmoothabilityPackagePLSmoothingExistenceFields :=
    smoothabilityPackagePLSmoothingExistenceFields_of_onePointRecognition
      recognize
  plSmoothingObstructionVanishing :=
    fun M _top _t2 _charted _simple _compact =>
      plSmoothingObstructionVanishing_of_onePointRecognition (recognize M)

/--
With obstruction vanishing supplied on the one-point route, the next package
field is the microbundle smoothing reduction.
-/
def OnePointRecognitionPLMicrobundleSmoothingPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLMicrobundleSmoothing M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingExistence_of_onePointRecognition h)
          (plSmoothingObstructionVanishing_of_onePointRecognition h)

/--
The one-point recognition route also supplies the microbundle smoothing
reduction for the recognized PL-smoothing inputs.
-/
theorem plMicrobundleSmoothing_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLMicrobundleSmoothing M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingExistence_of_onePointRecognition h)
      (plSmoothingObstructionVanishing_of_onePointRecognition h) :=
  HasPLMicrobundleSmoothing.ofOnePointRecognition h rfl rfl rfl rfl

/--
The one-point recognition route now closes the exact PL microbundle smoothing
payload that was previously the blocker.
-/
theorem onePointRecognition_plMicrobundleSmoothingPayload :
    OnePointRecognitionPLMicrobundleSmoothingPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plMicrobundleSmoothing_of_onePointRecognition h

/--
One-point recognition advances through the microbundle smoothing reduction.
-/
theorem plMicrobundleSmoothingFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h⟩

/-- The smoothability package fields through microbundle smoothing. -/
structure SmoothabilityPackagePLMicrobundleSmoothingFields extends
    SmoothabilityPackagePLSmoothingObstructionVanishingFields.{u} where
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

/--
Uniform one-point recognition constructs the package fields through
microbundle smoothing.
-/
theorem smoothabilityPackagePLMicrobundleSmoothingFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLMicrobundleSmoothingFields.{u} where
  toSmoothabilityPackagePLSmoothingObstructionVanishingFields :=
    smoothabilityPackagePLSmoothingObstructionVanishingFields_of_onePointRecognition
      recognize
  plMicrobundleSmoothing := fun M _top _t2 _charted _simple _compact =>
    plMicrobundleSmoothing_of_onePointRecognition (recognize M)

/--
With microbundle smoothing supplied on the one-point route, the next package
field is the PL-to-smooth smoothing theorem itself.
-/
def OnePointRecognitionPLSmoothingTheoremPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingTheorem M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)

/--
The one-point recognition route also supplies the PL-to-smooth smoothing theorem
for the recognized compatible PL atlas.
-/
theorem plSmoothingTheorem_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingTheorem M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h) :=
  HasPLSmoothingTheorem.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact PL smoothing theorem
payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingTheoremPayload :
    OnePointRecognitionPLSmoothingTheoremPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingTheorem_of_onePointRecognition h

/--
One-point recognition advances through the PL-to-smooth smoothing theorem.
-/
theorem plSmoothingTheoremFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
      HasPLSmoothingTheorem M triangulation plStructure plAtlas := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h⟩

/-- The smoothability package fields through the PL-to-smooth smoothing theorem. -/
structure SmoothabilityPackagePLSmoothingTheoremFields extends
    SmoothabilityPackagePLMicrobundleSmoothingFields.{u} where
  plSmoothing :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingTheorem M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)

/--
Uniform one-point recognition constructs the package fields through the
PL-to-smooth smoothing theorem.
-/
theorem smoothabilityPackagePLSmoothingTheoremFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingTheoremFields.{u} where
  toSmoothabilityPackagePLMicrobundleSmoothingFields :=
    smoothabilityPackagePLMicrobundleSmoothingFields_of_onePointRecognition
      recognize
  plSmoothing := fun M _top _t2 _charted _simple _compact =>
    plSmoothingTheorem_of_onePointRecognition (recognize M)

/--
With the PL-to-smooth theorem supplied on the one-point route, the next package
field is compatibility of the produced PL smoothing.
-/
def OnePointRecognitionPLSmoothingCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingCompatibility M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)

/--
The one-point recognition route also supplies compatibility of the produced PL
smoothing.
-/
theorem plSmoothingCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingCompatibility M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h) :=
  HasPLSmoothingCompatibility.ofOnePointRecognition h rfl rfl rfl

/--
The one-point recognition route now closes the exact PL smoothing compatibility
payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingCompatibilityPayload :
    OnePointRecognitionPLSmoothingCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingCompatibility_of_onePointRecognition h

/--
One-point recognition advances through PL smoothing compatibility.
-/
theorem plSmoothingCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
    ∃ plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas,
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through PL smoothing compatibility. -/
structure SmoothabilityPackagePLSmoothingCompatibilityFields extends
    SmoothabilityPackagePLSmoothingTheoremFields.{u} where
  plSmoothingCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)

/--
Uniform one-point recognition constructs the package fields through PL
smoothing compatibility.
-/
theorem smoothabilityPackagePLSmoothingCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingCompatibilityFields.{u} where
  toSmoothabilityPackagePLSmoothingTheoremFields :=
    smoothabilityPackagePLSmoothingTheoremFields_of_onePointRecognition recognize
  plSmoothingCompatibility := fun M _top _t2 _charted _simple _compact =>
    plSmoothingCompatibility_of_onePointRecognition (recognize M)

/--
With PL smoothing compatibility supplied on the one-point route, the next
package field is uniqueness of the selected PL smoothing.
-/
def OnePointRecognitionPLSmoothingUniquenessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingUniqueness M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)

/--
The one-point recognition route also supplies uniqueness of the selected PL
smoothing.
-/
theorem plSmoothingUniqueness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingUniqueness M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h) :=
  HasPLSmoothingUniqueness.ofOnePointRecognition h rfl rfl rfl

/--
The one-point recognition route now closes the exact PL smoothing uniqueness
payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingUniquenessPayload :
    OnePointRecognitionPLSmoothingUniquenessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingUniqueness_of_onePointRecognition h

/--
One-point recognition advances through PL smoothing uniqueness.
-/
theorem plSmoothingUniquenessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
    ∃ plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h⟩

/-- The smoothability package fields through PL smoothing uniqueness. -/
structure SmoothabilityPackagePLSmoothingUniquenessFields extends
    SmoothabilityPackagePLSmoothingCompatibilityFields.{u} where
  plSmoothingUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingUniqueness M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)

/--
Uniform one-point recognition constructs the package fields through PL
smoothing uniqueness.
-/
theorem smoothabilityPackagePLSmoothingUniquenessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingUniquenessFields.{u} where
  toSmoothabilityPackagePLSmoothingCompatibilityFields :=
    smoothabilityPackagePLSmoothingCompatibilityFields_of_onePointRecognition
      recognize
  plSmoothingUniqueness := fun M _top _t2 _charted _simple _compact =>
    plSmoothingUniqueness_of_onePointRecognition (recognize M)

/--
With PL smoothing uniqueness supplied on the one-point route, the next package
field is compatibility of the local smooth models supplied by PL smoothing.
-/
def OnePointRecognitionPLSmoothingLocalModelCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasPLSmoothingLocalModelCompatibility M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)

/--
The one-point recognition route also supplies compatibility of the local smooth
models produced by PL smoothing.
-/
theorem plSmoothingLocalModelCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasPLSmoothingLocalModelCompatibility M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h) :=
  HasPLSmoothingLocalModelCompatibility.ofOnePointRecognition h rfl rfl rfl

/--
The one-point recognition route now closes the exact PL smoothing local-model
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_plSmoothingLocalModelCompatibilityPayload :
    OnePointRecognitionPLSmoothingLocalModelCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact plSmoothingLocalModelCompatibility_of_onePointRecognition h

/--
One-point recognition advances through PL smoothing local-model compatibility.
-/
theorem plSmoothingLocalModelCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
    ∃ plSmoothing :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas,
    ∃ _plSmoothingCompatibility :
      HasPLSmoothingCompatibility
        M triangulation plStructure plAtlas plSmoothing,
    ∃ _plSmoothingUniqueness :
      HasPLSmoothingUniqueness
        M triangulation plStructure plAtlas plSmoothing,
      HasPLSmoothingLocalModelCompatibility
        M triangulation plStructure plAtlas plSmoothing := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through PL smoothing local-model compatibility. -/
structure SmoothabilityPackagePLSmoothingLocalModelCompatibilityFields extends
    SmoothabilityPackagePLSmoothingUniquenessFields.{u} where
  plSmoothingLocalModelCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasPLSmoothingLocalModelCompatibility M
          (moiseTriangulation M)
          (plStructure M)
          (plAtlas M)
          (plSmoothing M)

/--
Uniform one-point recognition constructs the package fields through PL
smoothing local-model compatibility.
-/
theorem smoothabilityPackagePLSmoothingLocalModelCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackagePLSmoothingLocalModelCompatibilityFields.{u} where
  toSmoothabilityPackagePLSmoothingUniquenessFields :=
    smoothabilityPackagePLSmoothingUniquenessFields_of_onePointRecognition
      recognize
  plSmoothingLocalModelCompatibility :=
    fun M _top _t2 _charted _simple _compact =>
      plSmoothingLocalModelCompatibility_of_onePointRecognition (recognize M)

/--
With PL smoothing local-model compatibility supplied on the one-point route,
the next package field is the actual smooth structure.
-/
def OnePointRecognitionSmoothStructurePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasThreeManifoldSmoothStructure M

/--
The one-point recognition route also supplies the smooth structure required by
the surgery layer.
-/
theorem smoothStructure_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasThreeManifoldSmoothStructure M :=
  HasThreeManifoldSmoothStructure.ofOnePointRecognition h

/--
The one-point recognition route now closes the exact smooth-structure payload
that was previously the blocker.
-/
theorem onePointRecognition_smoothStructurePayload :
    OnePointRecognitionSmoothStructurePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothStructure_of_onePointRecognition h

/--
One-point recognition advances through the smooth-structure witness.
-/
theorem smoothStructureFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
      HasThreeManifoldSmoothStructure M := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h⟩

/-- The smoothability package fields through the smooth-structure witness. -/
structure SmoothabilityPackageSmoothStructureFields extends
    SmoothabilityPackagePLSmoothingLocalModelCompatibilityFields.{u} where
  smoothStructure :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasThreeManifoldSmoothStructure M

/--
Uniform one-point recognition constructs the package fields through the
smooth-structure witness.
-/
theorem smoothabilityPackageSmoothStructureFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothStructureFields.{u} where
  toSmoothabilityPackagePLSmoothingLocalModelCompatibilityFields :=
    smoothabilityPackagePLSmoothingLocalModelCompatibilityFields_of_onePointRecognition
      recognize
  smoothStructure := fun M _top _t2 _charted _simple _compact =>
    smoothStructure_of_onePointRecognition (recognize M)

/--
With the smooth structure supplied on the one-point route, the next package
field is construction of the smooth atlas from the PL smoothing theorem.
-/
def OnePointRecognitionSmoothAtlasConstructionPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothAtlasConstruction M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)
          (smoothStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies construction of the smooth atlas
from the PL smoothing theorem.
-/
theorem smoothAtlasConstruction_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothAtlasConstruction M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h)
      (smoothStructure_of_onePointRecognition h) :=
  HasSmoothAtlasConstruction.ofOnePointRecognition h rfl rfl rfl rfl

/--
The one-point recognition route now closes the exact smooth-atlas construction
payload that was previously the blocker.
-/
theorem onePointRecognition_smoothAtlasConstructionPayload :
    OnePointRecognitionSmoothAtlasConstructionPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothAtlasConstruction_of_onePointRecognition h

/--
One-point recognition advances through construction of the smooth atlas.
-/
theorem smoothAtlasConstructionFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
      HasSmoothAtlasConstruction
        M triangulation plStructure plAtlas plSmoothing smoothStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-atlas construction. -/
structure SmoothabilityPackageSmoothAtlasConstructionFields extends
    SmoothabilityPackageSmoothStructureFields.{u} where
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

/--
Uniform one-point recognition constructs the package fields through
smooth-atlas construction.
-/
theorem smoothabilityPackageSmoothAtlasConstructionFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothAtlasConstructionFields.{u} where
  toSmoothabilityPackageSmoothStructureFields :=
    smoothabilityPackageSmoothStructureFields_of_onePointRecognition recognize
  smoothAtlasConstruction := fun M _top _t2 _charted _simple _compact =>
    smoothAtlasConstruction_of_onePointRecognition (recognize M)

/--
With smooth-atlas construction supplied on the one-point route, the next
package field is compatibility between that smooth atlas and the PL atlas.
-/
def OnePointRecognitionSmoothAtlasPLCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothAtlasPLCompatibility M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)
          (smoothStructure_of_onePointRecognition h)
          (smoothAtlasConstruction_of_onePointRecognition h)

/--
The one-point recognition route also supplies compatibility between the
constructed smooth atlas and the PL atlas.
-/
theorem smoothAtlasPLCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothAtlasPLCompatibility M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h)
      (smoothStructure_of_onePointRecognition h)
      (smoothAtlasConstruction_of_onePointRecognition h) :=
  HasSmoothAtlasPLCompatibility.ofOnePointRecognition h rfl rfl rfl rfl rfl

/--
The one-point recognition route now closes the exact smooth-atlas/PL-atlas
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_smoothAtlasPLCompatibilityPayload :
    OnePointRecognitionSmoothAtlasPLCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothAtlasPLCompatibility_of_onePointRecognition h

/--
One-point recognition advances through smooth-atlas/PL-atlas compatibility.
-/
theorem smoothAtlasPLCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-atlas/PL-atlas compatibility. -/
structure SmoothabilityPackageSmoothAtlasPLCompatibilityFields extends
    SmoothabilityPackageSmoothAtlasConstructionFields.{u} where
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
          (smoothAtlasConstruction M)

/--
Uniform one-point recognition constructs the package fields through
smooth-atlas/PL-atlas compatibility.
-/
theorem smoothabilityPackageSmoothAtlasPLCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothAtlasPLCompatibilityFields.{u} where
  toSmoothabilityPackageSmoothAtlasConstructionFields :=
    smoothabilityPackageSmoothAtlasConstructionFields_of_onePointRecognition
      recognize
  smoothAtlasPLCompatibility := fun M _top _t2 _charted _simple _compact =>
    smoothAtlasPLCompatibility_of_onePointRecognition (recognize M)

/--
With smooth-atlas/PL-atlas compatibility supplied on the one-point route, the
next package field is maximality of the produced smooth atlas.
-/
def OnePointRecognitionSmoothAtlasMaximalityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothAtlasMaximality M
          (moiseTriangulation_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)
          (smoothStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies maximality of the produced
smooth atlas.
-/
theorem smoothAtlasMaximality_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothAtlasMaximality M
      (moiseTriangulation_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h)
      (smoothStructure_of_onePointRecognition h) :=
  HasSmoothAtlasMaximality.ofOnePointRecognition h rfl rfl rfl rfl

/--
The one-point recognition route now closes the exact smooth-atlas maximality
payload that was previously the blocker.
-/
theorem onePointRecognition_smoothAtlasMaximalityPayload :
    OnePointRecognitionSmoothAtlasMaximalityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothAtlasMaximality_of_onePointRecognition h

/--
One-point recognition advances through smooth-atlas maximality.
-/
theorem smoothAtlasMaximalityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
    ∃ _smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h,
    smoothAtlasMaximality_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-atlas maximality. -/
structure SmoothabilityPackageSmoothAtlasMaximalityFields extends
    SmoothabilityPackageSmoothAtlasPLCompatibilityFields.{u} where
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

/--
Uniform one-point recognition constructs the package fields through
smooth-atlas maximality.
-/
theorem smoothabilityPackageSmoothAtlasMaximalityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothAtlasMaximalityFields.{u} where
  toSmoothabilityPackageSmoothAtlasPLCompatibilityFields :=
    smoothabilityPackageSmoothAtlasPLCompatibilityFields_of_onePointRecognition
      recognize
  smoothAtlasMaximality := fun M _top _t2 _charted _simple _compact =>
    smoothAtlasMaximality_of_onePointRecognition (recognize M)

/--
With smooth-atlas maximality supplied on the one-point route, the next package
field is uniqueness/compatibility of the produced smooth atlas.
-/
def OnePointRecognitionSmoothAtlasUniquenessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothAtlasUniqueness M (smoothStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies uniqueness/compatibility of the
produced smooth atlas.
-/
theorem smoothAtlasUniqueness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothAtlasUniqueness M (smoothStructure_of_onePointRecognition h) :=
  HasSmoothAtlasUniqueness.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact smooth-atlas uniqueness
payload that was previously the blocker.
-/
theorem onePointRecognition_smoothAtlasUniquenessPayload :
    OnePointRecognitionSmoothAtlasUniquenessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothAtlasUniqueness_of_onePointRecognition h

/--
One-point recognition advances through smooth-atlas uniqueness/compatibility.
-/
theorem smoothAtlasUniquenessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
    ∃ _smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
      HasSmoothAtlasUniqueness M smoothStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h,
    smoothAtlasMaximality_of_onePointRecognition h,
    smoothAtlasUniqueness_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-atlas uniqueness. -/
structure SmoothabilityPackageSmoothAtlasUniquenessFields extends
    SmoothabilityPackageSmoothAtlasMaximalityFields.{u} where
  smoothAtlasUniqueness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasUniqueness M (smoothStructure M)

/--
Uniform one-point recognition constructs the package fields through
smooth-atlas uniqueness/compatibility.
-/
theorem smoothabilityPackageSmoothAtlasUniquenessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothAtlasUniquenessFields.{u} where
  toSmoothabilityPackageSmoothAtlasMaximalityFields :=
    smoothabilityPackageSmoothAtlasMaximalityFields_of_onePointRecognition
      recognize
  smoothAtlasUniqueness := fun M _top _t2 _charted _simple _compact =>
    smoothAtlasUniqueness_of_onePointRecognition (recognize M)

/--
With smooth-atlas uniqueness supplied on the one-point route, the next package
field is uniqueness of the smooth structure up to diffeomorphism.
-/
def OnePointRecognitionSmoothStructureUniquenessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothStructureUniquenessUpToDiffeomorphism M
          (smoothStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies uniqueness of the smooth
structure up to diffeomorphism.
-/
theorem smoothStructureUniqueness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothStructureUniquenessUpToDiffeomorphism M
      (smoothStructure_of_onePointRecognition h) :=
  HasSmoothStructureUniquenessUpToDiffeomorphism.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact smooth-structure
uniqueness payload that was previously the blocker.
-/
theorem onePointRecognition_smoothStructureUniquenessPayload :
    OnePointRecognitionSmoothStructureUniquenessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothStructureUniqueness_of_onePointRecognition h

/--
One-point recognition advances through smooth-structure uniqueness.
-/
theorem smoothStructureUniquenessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
    ∃ _smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ _smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure,
      HasSmoothStructureUniquenessUpToDiffeomorphism
        M smoothStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h,
    smoothAtlasMaximality_of_onePointRecognition h,
    smoothAtlasUniqueness_of_onePointRecognition h,
    smoothStructureUniqueness_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-structure uniqueness. -/
structure SmoothabilityPackageSmoothStructureUniquenessFields extends
    SmoothabilityPackageSmoothAtlasUniquenessFields.{u} where
  smoothStructureUniquenessUpToDiffeomorphism :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothStructureUniquenessUpToDiffeomorphism M (smoothStructure M)

/--
Uniform one-point recognition constructs the package fields through
smooth-structure uniqueness.
-/
theorem smoothabilityPackageSmoothStructureUniquenessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothStructureUniquenessFields.{u} where
  toSmoothabilityPackageSmoothAtlasUniquenessFields :=
    smoothabilityPackageSmoothAtlasUniquenessFields_of_onePointRecognition
      recognize
  smoothStructureUniquenessUpToDiffeomorphism :=
    fun M _top _t2 _charted _simple _compact =>
      smoothStructureUniqueness_of_onePointRecognition (recognize M)

/--
With smooth-structure uniqueness supplied on the one-point route, the next
package field is smooth transition-map compatibility.
-/
def OnePointRecognitionSmoothTransitionCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothTransitionCompatibility M (smoothStructure_of_onePointRecognition h)

/--
The one-point recognition route also supplies smooth transition-map
compatibility.
-/
theorem smoothTransitionCompatibility_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothTransitionCompatibility M (smoothStructure_of_onePointRecognition h) :=
  HasSmoothTransitionCompatibility.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact smooth transition-map
compatibility payload that was previously the blocker.
-/
theorem onePointRecognition_smoothTransitionCompatibilityPayload :
    OnePointRecognitionSmoothTransitionCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothTransitionCompatibility_of_onePointRecognition h

/--
One-point recognition advances through smooth transition-map compatibility.
-/
theorem smoothTransitionCompatibilityFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
    ∃ _smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ _smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism
        M smoothStructure,
      HasSmoothTransitionCompatibility M smoothStructure := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h,
    smoothAtlasMaximality_of_onePointRecognition h,
    smoothAtlasUniqueness_of_onePointRecognition h,
    smoothStructureUniqueness_of_onePointRecognition h,
    smoothTransitionCompatibility_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth transition compatibility. -/
structure SmoothabilityPackageSmoothTransitionCompatibilityFields extends
    SmoothabilityPackageSmoothStructureUniquenessFields.{u} where
  smoothTransitionCompatibility :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothTransitionCompatibility M (smoothStructure M)

/--
Uniform one-point recognition constructs the package fields through smooth
transition-map compatibility.
-/
theorem smoothabilityPackageSmoothTransitionCompatibilityFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothTransitionCompatibilityFields.{u} where
  toSmoothabilityPackageSmoothStructureUniquenessFields :=
    smoothabilityPackageSmoothStructureUniquenessFields_of_onePointRecognition
      recognize
  smoothTransitionCompatibility := fun M _top _t2 _charted _simple _compact =>
    smoothTransitionCompatibility_of_onePointRecognition (recognize M)

/--
With smooth transition-map compatibility supplied on the one-point route, the
next package field is smoothness of all transition maps in the produced atlas.
-/
def OnePointRecognitionSmoothAtlasTransitionSmoothnessPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothAtlasTransitionSmoothness M
          (smoothStructure_of_onePointRecognition h)
          (smoothTransitionCompatibility_of_onePointRecognition h)

/--
The one-point recognition route also supplies smoothness of all transition maps
in the produced smooth atlas.
-/
theorem smoothAtlasTransitionSmoothness_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothAtlasTransitionSmoothness M
      (smoothStructure_of_onePointRecognition h)
      (smoothTransitionCompatibility_of_onePointRecognition h) :=
  HasSmoothAtlasTransitionSmoothness.ofOnePointRecognition h rfl rfl

/--
The one-point recognition route now closes the exact smooth-atlas transition
smoothness payload that was previously the blocker.
-/
theorem onePointRecognition_smoothAtlasTransitionSmoothnessPayload :
    OnePointRecognitionSmoothAtlasTransitionSmoothnessPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothAtlasTransitionSmoothness_of_onePointRecognition h

/--
One-point recognition advances through smooth-atlas transition smoothness.
-/
theorem smoothAtlasTransitionSmoothnessFields_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ localCharts : HasMoiseLocalTriangulationCharts M,
    ∃ _locallyFiniteCoverRefinement :
      HasMoiseLocallyFiniteCoverRefinement M localCharts,
    ∃ simplicialComplex : HasMoiseSimplicialComplex M localCharts,
    ∃ _compatibleChartTriangulations :
      HasMoiseCompatibleChartTriangulations M
        localCharts simplicialComplex,
    ∃ triangulation : HasMoiseTriangulation M,
    ∃ _simplicialApproximation :
      HasMoiseSimplicialApproximation M
        localCharts simplicialComplex triangulation,
    ∃ _starNeighborhoodBasis :
      HasMoiseStarNeighborhoodBasis M localCharts triangulation,
    ∃ _barycentricSubdivision :
      HasMoiseBarycentricSubdivisionControl M triangulation,
    ∃ _regularNeighborhoodCompatibility :
      HasMoiseRegularNeighborhoodCompatibility M triangulation,
    ∃ _triangulationLocalFiniteness :
      HasMoiseTriangulationLocalFiniteness M triangulation,
    ∃ linkCompatibility : HasMoiseLinkCompatibility M triangulation,
    ∃ _plManifoldRecognition :
      HasMoisePLManifoldRecognition M
        triangulation linkCompatibility,
    ∃ _triangulationHomeomorphism :
      HasMoiseTriangulationHomeomorphism M
        localCharts triangulation,
    ∃ _triangulationCompatibility :
      HasMoiseTriangulationCompatibility M
        localCharts triangulation,
    ∃ triangulationUniqueness :
      HasMoiseTriangulationUniqueness M triangulation,
    ∃ _hauptvermutungDimensionThree :
      HasMoiseHauptvermutungDimensionThree M
        triangulation triangulationUniqueness,
    ∃ plStructure :
      HasCompatiblePLStructure M triangulation,
    ∃ _plTransitionCompatibility :
      HasPLTransitionCompatibility M triangulation plStructure,
    ∃ plAtlas :
      HasCompatiblePLAtlas M triangulation plStructure,
    ∃ _plManifoldAtlas :
      HasPLManifoldAtlas M triangulation plStructure plAtlas,
    ∃ _plCollarNeighborhoodCompatibility :
      HasPLCollarNeighborhoodCompatibility M triangulation plStructure plAtlas,
    ∃ _plHomeomorphismCompatibility :
      HasPLHomeomorphismCompatibility
        M localCharts triangulation plStructure plAtlas,
    ∃ _plAtlasMaximality :
      HasPLAtlasMaximality M triangulation plStructure plAtlas,
    ∃ plSmoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas,
    ∃ plSmoothingObstructionVanishing :
      HasPLSmoothingObstructionVanishing M triangulation plStructure plAtlas,
    ∃ _plMicrobundleSmoothing :
      HasPLMicrobundleSmoothing M
        triangulation plStructure plAtlas plSmoothingExistence
        plSmoothingObstructionVanishing,
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
    ∃ _smoothAtlasPLCompatibility :
      HasSmoothAtlasPLCompatibility
        M triangulation plStructure plAtlas plSmoothing smoothStructure
        smoothAtlasConstruction,
    ∃ _smoothAtlasMaximality :
      HasSmoothAtlasMaximality
        M triangulation plStructure plAtlas plSmoothing smoothStructure,
    ∃ _smoothAtlasUniqueness :
      HasSmoothAtlasUniqueness M smoothStructure,
    ∃ _smoothStructureUniqueness :
      HasSmoothStructureUniquenessUpToDiffeomorphism
        M smoothStructure,
    ∃ smoothTransitionCompatibility :
      HasSmoothTransitionCompatibility M smoothStructure,
      HasSmoothAtlasTransitionSmoothness
        M smoothStructure smoothTransitionCompatibility := by
  exact ⟨moiseLocalCharts_of_onePointRecognition h,
    moiseLocallyFiniteCoverRefinement_of_onePointRecognition h,
    moiseSimplicialComplex_of_onePointRecognition h,
    moiseCompatibleChartTriangulations_of_onePointRecognition h,
    moiseTriangulation_of_onePointRecognition h,
    moiseSimplicialApproximation_of_onePointRecognition h,
    moiseStarNeighborhoodBasis_of_onePointRecognition h,
    moiseBarycentricSubdivisionControl_of_onePointRecognition h,
    moiseRegularNeighborhoodCompatibility_of_onePointRecognition h,
    moiseTriangulationLocalFiniteness_of_onePointRecognition h,
    moiseLinkCompatibility_of_onePointRecognition h,
    moisePLManifoldRecognition_of_onePointRecognition h,
    moiseTriangulationHomeomorphism_of_onePointRecognition h,
    moiseTriangulationCompatibility_of_onePointRecognition h,
    moiseTriangulationUniqueness_of_onePointRecognition h,
    moiseHauptvermutungDimensionThree_of_onePointRecognition h,
    compatiblePLStructure_of_onePointRecognition h,
    plTransitionCompatibility_of_onePointRecognition h,
    compatiblePLAtlas_of_onePointRecognition h,
    plManifoldAtlas_of_onePointRecognition h,
    plCollarNeighborhoodCompatibility_of_onePointRecognition h,
    plHomeomorphismCompatibility_of_onePointRecognition h,
    plAtlasMaximality_of_onePointRecognition h,
    plSmoothingExistence_of_onePointRecognition h,
    plSmoothingObstructionVanishing_of_onePointRecognition h,
    plMicrobundleSmoothing_of_onePointRecognition h,
    plSmoothingTheorem_of_onePointRecognition h,
    plSmoothingCompatibility_of_onePointRecognition h,
    plSmoothingUniqueness_of_onePointRecognition h,
    plSmoothingLocalModelCompatibility_of_onePointRecognition h,
    smoothStructure_of_onePointRecognition h,
    smoothAtlasConstruction_of_onePointRecognition h,
    smoothAtlasPLCompatibility_of_onePointRecognition h,
    smoothAtlasMaximality_of_onePointRecognition h,
    smoothAtlasUniqueness_of_onePointRecognition h,
    smoothStructureUniqueness_of_onePointRecognition h,
    smoothTransitionCompatibility_of_onePointRecognition h,
    smoothAtlasTransitionSmoothness_of_onePointRecognition h⟩

/-- The smoothability package fields through smooth-atlas transition smoothness. -/
structure SmoothabilityPackageSmoothAtlasTransitionSmoothnessFields extends
    SmoothabilityPackageSmoothTransitionCompatibilityFields.{u} where
  smoothAtlasTransitionSmoothness :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace ThreeManifoldModel M]
      [SimplyConnectedSpace M] [CompactSpace M],
        HasSmoothAtlasTransitionSmoothness M
          (smoothStructure M)
          (smoothTransitionCompatibility M)

/--
Uniform one-point recognition constructs the package fields through
smooth-atlas transition smoothness.
-/
theorem smoothabilityPackageSmoothAtlasTransitionSmoothnessFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothAtlasTransitionSmoothnessFields.{u} where
  toSmoothabilityPackageSmoothTransitionCompatibilityFields :=
    smoothabilityPackageSmoothTransitionCompatibilityFields_of_onePointRecognition
      recognize
  smoothAtlasTransitionSmoothness :=
    fun M _top _t2 _charted _simple _compact =>
      smoothAtlasTransitionSmoothness_of_onePointRecognition (recognize M)

/--
With smooth-atlas transition smoothness supplied on the one-point route, the
next package field is derivation of the smooth structure from the named inputs.
-/
def OnePointRecognitionSmoothStructureDerivationPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) →
        HasSmoothStructureDerivation M
          (moiseLocalCharts_of_onePointRecognition h)
          (moiseLocallyFiniteCoverRefinement_of_onePointRecognition h)
          (moiseSimplicialComplex_of_onePointRecognition h)
          (moiseCompatibleChartTriangulations_of_onePointRecognition h)
          (moiseTriangulation_of_onePointRecognition h)
          (moiseSimplicialApproximation_of_onePointRecognition h)
          (moiseStarNeighborhoodBasis_of_onePointRecognition h)
          (moiseBarycentricSubdivisionControl_of_onePointRecognition h)
          (moiseRegularNeighborhoodCompatibility_of_onePointRecognition h)
          (moiseTriangulationLocalFiniteness_of_onePointRecognition h)
          (moiseLinkCompatibility_of_onePointRecognition h)
          (moisePLManifoldRecognition_of_onePointRecognition h)
          (moiseTriangulationHomeomorphism_of_onePointRecognition h)
          (moiseTriangulationCompatibility_of_onePointRecognition h)
          (moiseTriangulationUniqueness_of_onePointRecognition h)
          (moiseHauptvermutungDimensionThree_of_onePointRecognition h)
          (compatiblePLStructure_of_onePointRecognition h)
          (plTransitionCompatibility_of_onePointRecognition h)
          (compatiblePLAtlas_of_onePointRecognition h)
          (plManifoldAtlas_of_onePointRecognition h)
          (plCollarNeighborhoodCompatibility_of_onePointRecognition h)
          (plHomeomorphismCompatibility_of_onePointRecognition h)
          (plAtlasMaximality_of_onePointRecognition h)
          (plSmoothingExistence_of_onePointRecognition h)
          (plSmoothingObstructionVanishing_of_onePointRecognition h)
          (plMicrobundleSmoothing_of_onePointRecognition h)
          (plSmoothingTheorem_of_onePointRecognition h)
          (plSmoothingCompatibility_of_onePointRecognition h)
          (plSmoothingUniqueness_of_onePointRecognition h)
          (plSmoothingLocalModelCompatibility_of_onePointRecognition h)
          (smoothStructure_of_onePointRecognition h)
          (smoothAtlasConstruction_of_onePointRecognition h)
          (smoothAtlasPLCompatibility_of_onePointRecognition h)
          (smoothAtlasMaximality_of_onePointRecognition h)
          (smoothAtlasUniqueness_of_onePointRecognition h)
          (smoothStructureUniqueness_of_onePointRecognition h)
          (smoothTransitionCompatibility_of_onePointRecognition h)
          (smoothAtlasTransitionSmoothness_of_onePointRecognition h)

/--
The one-point recognition route also supplies derivation of the smooth
structure from the named Moise, PL, smoothing, and smooth-atlas inputs.
-/
theorem smoothStructureDerivation_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    HasSmoothStructureDerivation M
      (moiseLocalCharts_of_onePointRecognition h)
      (moiseLocallyFiniteCoverRefinement_of_onePointRecognition h)
      (moiseSimplicialComplex_of_onePointRecognition h)
      (moiseCompatibleChartTriangulations_of_onePointRecognition h)
      (moiseTriangulation_of_onePointRecognition h)
      (moiseSimplicialApproximation_of_onePointRecognition h)
      (moiseStarNeighborhoodBasis_of_onePointRecognition h)
      (moiseBarycentricSubdivisionControl_of_onePointRecognition h)
      (moiseRegularNeighborhoodCompatibility_of_onePointRecognition h)
      (moiseTriangulationLocalFiniteness_of_onePointRecognition h)
      (moiseLinkCompatibility_of_onePointRecognition h)
      (moisePLManifoldRecognition_of_onePointRecognition h)
      (moiseTriangulationHomeomorphism_of_onePointRecognition h)
      (moiseTriangulationCompatibility_of_onePointRecognition h)
      (moiseTriangulationUniqueness_of_onePointRecognition h)
      (moiseHauptvermutungDimensionThree_of_onePointRecognition h)
      (compatiblePLStructure_of_onePointRecognition h)
      (plTransitionCompatibility_of_onePointRecognition h)
      (compatiblePLAtlas_of_onePointRecognition h)
      (plManifoldAtlas_of_onePointRecognition h)
      (plCollarNeighborhoodCompatibility_of_onePointRecognition h)
      (plHomeomorphismCompatibility_of_onePointRecognition h)
      (plAtlasMaximality_of_onePointRecognition h)
      (plSmoothingExistence_of_onePointRecognition h)
      (plSmoothingObstructionVanishing_of_onePointRecognition h)
      (plMicrobundleSmoothing_of_onePointRecognition h)
      (plSmoothingTheorem_of_onePointRecognition h)
      (plSmoothingCompatibility_of_onePointRecognition h)
      (plSmoothingUniqueness_of_onePointRecognition h)
      (plSmoothingLocalModelCompatibility_of_onePointRecognition h)
      (smoothStructure_of_onePointRecognition h)
      (smoothAtlasConstruction_of_onePointRecognition h)
      (smoothAtlasPLCompatibility_of_onePointRecognition h)
      (smoothAtlasMaximality_of_onePointRecognition h)
      (smoothAtlasUniqueness_of_onePointRecognition h)
      (smoothStructureUniqueness_of_onePointRecognition h)
      (smoothTransitionCompatibility_of_onePointRecognition h)
      (smoothAtlasTransitionSmoothness_of_onePointRecognition h) :=
  HasSmoothStructureDerivation.ofOnePointRecognition h rfl

/--
The one-point recognition route now closes the exact smooth-structure
derivation payload that was previously the blocker.
-/
theorem onePointRecognition_smoothStructureDerivationPayload :
    OnePointRecognitionSmoothStructureDerivationPayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact smoothStructureDerivation_of_onePointRecognition h

/--
The closed one-point derivation interface packages into the theorem-shaped
`SmoothStructureDerivationStatement` consumed by the bridge.
-/
theorem smoothStructureDerivationStatement_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    SmoothStructureDerivationStatement M (smoothStructure_of_onePointRecognition h) :=
  smooth_structure_derivation_statement_of_components M
    (moiseLocalCharts_of_onePointRecognition h)
    (moiseLocallyFiniteCoverRefinement_of_onePointRecognition h)
    (moiseSimplicialComplex_of_onePointRecognition h)
    (moiseCompatibleChartTriangulations_of_onePointRecognition h)
    (moiseTriangulation_of_onePointRecognition h)
    (moiseSimplicialApproximation_of_onePointRecognition h)
    (moiseStarNeighborhoodBasis_of_onePointRecognition h)
    (moiseBarycentricSubdivisionControl_of_onePointRecognition h)
    (moiseRegularNeighborhoodCompatibility_of_onePointRecognition h)
    (moiseTriangulationLocalFiniteness_of_onePointRecognition h)
    (moiseLinkCompatibility_of_onePointRecognition h)
    (moisePLManifoldRecognition_of_onePointRecognition h)
    (moiseTriangulationHomeomorphism_of_onePointRecognition h)
    (moiseTriangulationCompatibility_of_onePointRecognition h)
    (moiseTriangulationUniqueness_of_onePointRecognition h)
    (moiseHauptvermutungDimensionThree_of_onePointRecognition h)
    (compatiblePLStructure_of_onePointRecognition h)
    (plTransitionCompatibility_of_onePointRecognition h)
    (compatiblePLAtlas_of_onePointRecognition h)
    (plManifoldAtlas_of_onePointRecognition h)
    (plCollarNeighborhoodCompatibility_of_onePointRecognition h)
    (plHomeomorphismCompatibility_of_onePointRecognition h)
    (plAtlasMaximality_of_onePointRecognition h)
    (plSmoothingExistence_of_onePointRecognition h)
    (plSmoothingObstructionVanishing_of_onePointRecognition h)
    (plMicrobundleSmoothing_of_onePointRecognition h)
    (plSmoothingTheorem_of_onePointRecognition h)
    (plSmoothingCompatibility_of_onePointRecognition h)
    (plSmoothingUniqueness_of_onePointRecognition h)
    (plSmoothingLocalModelCompatibility_of_onePointRecognition h)
    (smoothStructure_of_onePointRecognition h)
    (smoothAtlasConstruction_of_onePointRecognition h)
    (smoothAtlasPLCompatibility_of_onePointRecognition h)
    (smoothAtlasMaximality_of_onePointRecognition h)
    (smoothAtlasUniqueness_of_onePointRecognition h)
    (smoothStructureUniqueness_of_onePointRecognition h)
    (smoothTransitionCompatibility_of_onePointRecognition h)
    (smoothAtlasTransitionSmoothness_of_onePointRecognition h)
    (smoothStructureDerivation_of_onePointRecognition h)

/-- The smoothability package fields through smooth-structure derivation. -/
structure SmoothabilityPackageSmoothStructureDerivationFields extends
    SmoothabilityPackageSmoothAtlasTransitionSmoothnessFields.{u} where
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

/--
Uniform one-point recognition constructs the package fields through
smooth-structure derivation.
-/
theorem smoothabilityPackageSmoothStructureDerivationFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageSmoothStructureDerivationFields.{u} where
  toSmoothabilityPackageSmoothAtlasTransitionSmoothnessFields :=
    smoothabilityPackageSmoothAtlasTransitionSmoothnessFields_of_onePointRecognition
      recognize
  smoothStructureDerivation := fun M _top _t2 _charted _simple _compact =>
    smoothStructureDerivation_of_onePointRecognition (recognize M)

/--
After the full one-point smooth-structure derivation is available, the next
package datum is the theorem-shaped bridge from that derivation statement to
the surgery-layer `IsManifold` instance.
-/
def SmoothabilityBridgeTheoremPayload : Prop :=
  SmoothabilityBridgeStatement.{u}

/-- A completed package supplies the next theorem-shaped smoothability bridge. -/
theorem smoothabilityPackage_requires_smoothabilityBridge
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityBridgeTheoremPayload.{u} :=
  package.bridge

/--
The exact ambient theorem needed to turn one-point recognition into the package
bridge: for the charted-space instance already in scope, a one-point recognized
target must carry the surgery-layer `IsManifold` evidence.
-/
def OnePointRecognitionAmbientSmoothabilityBridgePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        IsManifold ThreeManifoldModelWithCorners 1 M

/--
The ambient one-point smoothability payload supplies the theorem-shaped package
bridge by eliminating the stored smooth-structure constructor.
-/
theorem smoothabilityBridgeStatement_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    (payload :
      OnePointRecognitionAmbientSmoothabilityBridgePayload.{u}) :
    SmoothabilityBridgeStatement.{u} := by
  intro M _top _t2 _charted _simple _compact smoothStructure
    _smoothStructureDerivation
  cases smoothStructure with
  | ofOnePointRecognition h =>
      exact payload h

/--
Conversely, the theorem-shaped bridge supplies the exact ambient one-point
smoothability payload by applying it to the one-point smooth structure and its
closed derivation statement.
-/
theorem onePointRecognitionAmbientSmoothabilityBridgePayload_of_smoothabilityBridgeStatement
    (bridge : SmoothabilityBridgeStatement.{u}) :
    OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  exact bridge M (smoothStructure_of_onePointRecognition h)
    (smoothStructureDerivationStatement_of_onePointRecognition h)

/--
Thus the package bridge is equivalent to the ambient one-point-recognition
`IsManifold` payload for the charted-space instance already in scope.
-/
theorem smoothabilityBridgeStatement_iff_onePointRecognitionAmbientSmoothabilityBridgePayload :
    SmoothabilityBridgeStatement.{u} ↔
      OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} :=
  ⟨onePointRecognitionAmbientSmoothabilityBridgePayload_of_smoothabilityBridgeStatement,
    smoothabilityBridgeStatement_of_onePointRecognitionAmbientSmoothabilityBridgePayload⟩

/--
A sharper source-level formulation: it is enough to know that the ambient
charted-space instance agrees with the transported one-point compactification
charted space used by `SmoothabilityOnePointRecognition`.
-/
def OnePointRecognitionAmbientChartedSpaceCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        (inferInstance : ChartedSpace ThreeManifoldModel M) =
          homeomorphToOnePoint_threeSpace_smoothChartedSpace e

/--
A weaker atlas-level comparison source: the ambient atlas agrees with the
transported one-point atlas, even if the whole `ChartedSpace` structure has
not been identified.
-/
def OnePointRecognitionAmbientAtlasCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M =
          @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
One-sided atlas-level membership source: every ambient atlas chart is a chart
of the transported one-point atlas.  This is the exact atlas inclusion needed
for the current forward-compatibility route, without asserting equality of the
whole charted-space structure or any arbitrary `chartAt` choice.
-/
def OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M ⊆
          @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Generator-level source for the one-sided inclusion: every ambient atlas chart
is one of the canonical charts selected by the transported one-point charted
space.  This avoids asserting that an arbitrary chart containing a point is the
`chartAt` chosen at that same point.
-/
def OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              c =
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
The concrete chart generator used by `IsLocalHomeomorph.chartedSpace` in the
transported one-point charted-space construction.
-/
noncomputable def homeomorphToOnePoint_threeSpace_transportedLocalInverseChart
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    OpenPartialHomeomorph M ThreeManifoldModel :=
  (e.symm.isLocalHomeomorph.localInverseAt
    (e.symm.surjective.hasRightInverse.choose q)).trans
    (@ChartedSpace.chartAt ThreeManifoldModel _
      (OnePoint (EuclideanSpace ℝ (Fin 3))) _
      onePoint_threeSpace_smoothChartedSpace
      (e.symm.surjective.hasRightInverse.choose q))

/--
Lower constructor-level source for the generator payload: every ambient atlas
chart is one of the local-inverse charts explicitly generated by the
transported one-point charted-space constructor.
-/
def OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              c = homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q

/--
Field-level generator source for the transported local-inverse chart premise:
the arbitrary ambient atlas is exactly the range generated by
`IsLocalHomeomorph.chartedSpace` for the recognition homeomorphism.
-/
def OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M =
          Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e)

/--
Core atlas-field formulation of the transported local-inverse generator range:
it removes the recognition-side hypotheses that are irrelevant to the
charted-space atlas field comparison.
-/
def OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M =
          Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e)

/--
Core one-sided atlas-field comparison: every ambient atlas chart is already a
chart of the transported one-point charted space.
-/
def OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M ⊆
          @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Core generator-level source for the one-sided inclusion: every ambient atlas
chart is one of the canonical `chartAt` charts selected by the transported
one-point charted-space construction.
-/
def OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              c =
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
Core generator source for the arbitrary ambient charted-space field: every
ambient atlas chart is selected by the ambient `chartAt` function.
-/
def OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q

/--
Source-pointed selector-generation form: every ambient atlas chart is selected
by the ambient `chartAt` function at a point of that chart's own source.
-/
def OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              q ∈ c.source ∧
                c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q

/--
Source-existence part of the source-pointed selector invariant: every ambient
atlas chart has a point in its source.
-/
def OnePointRecognitionAmbientAtlasChartSourcePointCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M, q ∈ c.source

/--
Selector-choice part of the source-pointed selector invariant: at every point
of an ambient atlas chart's source, the ambient `chartAt` selector chooses that
chart.
-/
def OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ {q : M},
              q ∈ c.source →
                c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q

/--
Set-theoretic form of the ambient selector-generation claim: every ambient
atlas chart lies in the range of the ambient selected-chart function.
-/
def OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      atlas ThreeManifoldModel M ⊆
        Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance)

/--
The automatic direction supplied by the `ChartedSpace` API: every selected
ambient `chartAt` lies in the ambient atlas.
-/
def OnePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance) ⊆
        atlas ThreeManifoldModel M

/--
Exact field-level form of the remaining ambient generator claim: the ambient
atlas must be precisely the range of its selected-chart function.
-/
def OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      atlas ThreeManifoldModel M =
        Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance)

/--
Core reverse atlas-field comparison: every chart generated by the transported
one-point charted space lies in the ambient atlas.
-/
def OnePointRecognitionTransportedAtlasSubsetAmbientAtlasCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) ⊆
          atlas ThreeManifoldModel M

/--
One direction of the core atlas-field comparison: every ambient atlas chart is
generated by the transported local-inverse chart constructor.
-/
def OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M ⊆
          Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e)

/--
Source-conditioned forward local-inverse range inclusion: an ambient atlas chart
is required to lie in the transported local-inverse chart range once it is known
to have a point in its source.
-/
def OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            (∃ q : M, q ∈ c.source) →
              c ∈ Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e)

/--
The reverse direction of the core atlas-field comparison: every transported
local-inverse chart generator is present in the ambient atlas.
-/
def OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) ⊆
          atlas ThreeManifoldModel M

/--
The complementary field-level comparison needed to identify the arbitrary
ambient charted-space instance with the transported one-point charted space:
their selected `chartAt` functions must also agree.
-/
def OnePointRecognitionAmbientChartAtCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance =
          @ChartedSpace.chartAt ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Core selected-chart field comparison: the ambient `chartAt` selector agrees
with the transported one-point charted-space selector.
-/
def OnePointRecognitionAmbientChartAtCompatibilityCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance =
          @ChartedSpace.chartAt ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Pointwise core selected-chart comparison: at each source point, the ambient
selected chart is the transported one-point selected chart.
-/
def OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ q : M,
          @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q =
            @ChartedSpace.chartAt ThreeManifoldModel _ M _
              (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
Selected-source form of ambient/transported `chartAt` compatibility: the
current generator route only needs selector compatibility at source points
where the ambient selector is known to choose the ambient atlas chart.
-/
def OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ {q : M},
              q ∈ c.source →
                c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q →
                  @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q =
                    @ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
Direct source-pointed transported selector-generation form: every ambient atlas
chart is selected by the transported one-point `chartAt` function at a point of
that chart's own source.
-/
def OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              q ∈ c.source ∧
                c =
                  @ChartedSpace.chartAt ThreeManifoldModel _ M _
                    (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
Constructor-level source-pointed transported selector-generation form: every
ambient atlas chart is one of the explicit local-inverse charts generated by the
transported one-point charted-space constructor, at a point of that chart's own
source.
-/
def OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∃ q : M,
              q ∈ c.source ∧
                c = homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q

/--
Full charted-space compatibility supplies the atlas-level comparison.
-/
theorem onePointRecognitionAmbientAtlasCompatibilityPayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  have hEq :
      _charted = homeomorphToOnePoint_threeSpace_smoothChartedSpace e :=
    compat e
  change
    @atlas ThreeManifoldModel _ M _ _charted =
      @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
  rw [hEq]

/--
Atlas equality supplies the one-sided atlas inclusion used by the current
forward-compatibility route.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_ambientAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  have hAtlas :
      atlas ThreeManifoldModel M =
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e
  simpa [hAtlas] using hc

/--
Full charted-space compatibility also supplies the one-sided atlas inclusion.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} :=
  onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_ambientAtlasCompatibility
    (onePointRecognitionAmbientAtlasCompatibilityPayload_of_chartedSpaceCompatibility
      compat)

/--
If every ambient atlas chart is generated by the transported charted-space
selector, then it is in the transported atlas by `chart_mem_atlas`.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_generatedByTransportedChartAt
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  rcases generated e hc with ⟨q, hq⟩
  rw [hq]
  exact
    @chart_mem_atlas ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
The explicit local-inverse chart generator is exactly the transported
charted-space `chartAt` selected at the same source point.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q =
      @ChartedSpace.chartAt ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q := by
  rfl

/--
The transported one-point charted-space atlas is definitionally the range of
its local-inverse chart generator.
-/
theorem homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) =
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  rfl

/--
Each explicit transported local-inverse chart is, tautologically, in the range
of the transported local-inverse chart constructor.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_range
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q ∈
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  exact ⟨q, rfl⟩

/--
Each explicit transported local-inverse chart is an atlas chart for the
transported one-point charted space.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_smoothChartedSpace_atlas
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q ∈
      @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) := by
  rw [homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt]
  exact
    @chart_mem_atlas ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
The source point used to select the transported local-inverse chart belongs to
that chart's source.
-/
theorem homeomorphToOnePoint_threeSpace_mem_transportedLocalInverseChart_source
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    q ∈ (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q).source := by
  have hSource :
      q ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q).source :=
    @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q
  simp [homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt,
    hSource]

/--
Every explicit transported local-inverse chart has a nonempty source, witnessed
by the point at which it is selected.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_source_nonempty
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    ∃ x : M, x ∈ (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q).source := by
  exact
    ⟨q, homeomorphToOnePoint_threeSpace_mem_transportedLocalInverseChart_source e q⟩

/--
The transported one-point `chartAt` chart lies in the explicit local-inverse
chart range at the same point.
-/
theorem homeomorphToOnePoint_threeSpace_transportedChartAt_mem_transportedLocalInverseChart_range
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q ∈
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  rw [← homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q]
  exact homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_range e q

/--
Any chart identified with the transported one-point `chartAt` at `q` lies in
the explicit transported local-inverse chart range.
-/
theorem homeomorphToOnePoint_threeSpace_chart_eq_transportedChartAt_mem_transportedLocalInverseChart_range
    {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
    {c : OpenPartialHomeomorph M ThreeManifoldModel} {q : M}
    (hc :
      c =
        @ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q) :
    c ∈ Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  rw [hc]
  exact homeomorphToOnePoint_threeSpace_transportedChartAt_mem_transportedLocalInverseChart_range e q

/--
If the ambient selected chart agrees with the transported one-point selected
chart, then the ambient selected chart lies in the explicit transported
local-inverse chart range.
-/
theorem homeomorphToOnePoint_threeSpace_ambientChartAt_mem_transportedLocalInverseChart_range_of_chartAtCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q ∈
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  rw [chartAtCompat e]
  exact homeomorphToOnePoint_threeSpace_transportedChartAt_mem_transportedLocalInverseChart_range e q

/--
Field-level selected-chart compatibility identifies each transported
local-inverse chart with the ambient selected chart at the same point.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_ambientChartAt_of_chartAtCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q =
      @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q := by
  exact
    (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q).trans
      (congrFun (chartAtCompat e) q).symm

/--
The pointwise ambient/transported selected-chart compatibility gives the same
range membership for the ambient selected chart.
-/
theorem homeomorphToOnePoint_threeSpace_ambientChartAt_mem_transportedLocalInverseChart_range_of_pointwiseCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q ∈
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  exact
    homeomorphToOnePoint_threeSpace_chart_eq_transportedChartAt_mem_transportedLocalInverseChart_range
      e (chartAtCompat e q)

/--
If an ambient atlas chart is the ambient selected chart at a source point, and
the ambient selected chart agrees there with the transported selected chart,
then the chart lies in the transported local-inverse chart range.
-/
theorem homeomorphToOnePoint_threeSpace_chart_eq_ambientChartAt_mem_transportedLocalInverseChart_range_of_selectedSourceCompatibilityCore
    (selectedCompat :
      OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
    {c : OpenPartialHomeomorph M ThreeManifoldModel}
    (hcAtlas : c ∈ atlas ThreeManifoldModel M)
    {q : M} (hq : q ∈ c.source)
    (hselect : c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q) :
    c ∈ Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
  have hcompat :
      @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q =
        @ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q :=
    selectedCompat e hcAtlas hq hselect
  exact
    homeomorphToOnePoint_threeSpace_chart_eq_transportedChartAt_mem_transportedLocalInverseChart_range
      e (hselect.trans hcompat)

/--
Selector choice on atlas-chart sources plus selected-source compatibility
constructs the source-nonempty local-inverse range input.
-/
theorem onePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload_of_chartAtSelectsAtlasChartOnSourceCore_and_selectedSourceCompatibilityCore
    (selects :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u})
    (selectedCompat :
      OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc hsource
  rcases hsource with ⟨q, hq⟩
  exact
    homeomorphToOnePoint_threeSpace_chart_eq_ambientChartAt_mem_transportedLocalInverseChart_range_of_selectedSourceCompatibilityCore
      selectedCompat e hc hq (selects hc hq)

/--
If every ambient atlas chart is selected by the ambient `chartAt` at one of its
source points, then pointwise ambient/transported selected-chart compatibility
constructs the source-nonempty local-inverse range input.
-/
theorem onePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc _hsource
  rcases selected hc with ⟨q, _hqSource, hq⟩
  exact
    homeomorphToOnePoint_threeSpace_chart_eq_transportedChartAt_mem_transportedLocalInverseChart_range
      e (hq.trans (chartAtCompat e q))

/--
Source-pointed ambient selected-chart generation plus pointwise selected-chart
compatibility directly gives source-pointed transported `chartAt` generation.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected hc with ⟨q, hqSource, hq⟩
  refine ⟨q, hqSource, ?_⟩
  exact hq.trans (chartAtCompat e q)

/--
The same selected-chart data gives source-pointed generation by the explicit
transported local-inverse chart constructor.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected hc with ⟨q, hqSource, hq⟩
  refine ⟨q, hqSource, ?_⟩
  exact
    (hq.trans (chartAtCompat e q)).trans
      (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q).symm

/--
The selected ambient chart plus pointwise ambient/transported `chartAt`
compatibility gives the one-sided inclusion into the transported local-inverse
chart range.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected hc with ⟨q, hqSource, _hq⟩
  exact
    onePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
      selected chartAtCompat e hc ⟨q, hqSource⟩

/--
The same data gives generation by the transported `chartAt` selector.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected hc with ⟨q, _hqSource, hq⟩
  exact ⟨q, hq.trans (chartAtCompat e q)⟩

/--
Generation by the transported `chartAt` selector gives the one-sided inclusion
of the ambient atlas into the transported atlas.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected hc with ⟨q, _hqSource, hq⟩
  rw [hq, chartAtCompat e q]
  exact
    @chart_mem_atlas ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
The core atlas-field range comparison supplies the current recognition-shaped
range payload.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload_of_core
    (core :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  exact core e

/--
The core transported-`chartAt` generator source supplies the recognition-shaped
generator payload.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload_of_generatedByTransportedChartAtCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  exact generated e hc

/--
The core selected-chart comparison supplies the recognition-shaped selected
chart comparison.
-/
theorem onePointRecognitionAmbientChartAtCompatibilityPayload_of_chartAtCompatibilityCore
    (payload :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientChartAtCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  exact payload e

/--
Pointwise selected-chart compatibility supplies equality of the selected-chart
fields.
-/
theorem onePointRecognitionAmbientChartAtCompatibilityCorePayload_of_pointwiseCompatibilityCore
    (payload :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u} := by
  intro M _top _charted e
  funext q
  exact payload e q

/--
Field equality of selected charts supplies the pointwise formulation.
-/
theorem onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore
    (payload :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} := by
  intro M _top _charted e q
  rw [payload e]

/--
The selected-chart field comparison is exactly its pointwise form.
-/
theorem onePointRecognitionAmbientChartAtCompatibilityCorePayload_iff_pointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u} ↔
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} :=
  ⟨onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore,
    onePointRecognitionAmbientChartAtCompatibilityCorePayload_of_pointwiseCompatibilityCore⟩

/--
Global pointwise selected-chart compatibility supplies the weaker
selected-source compatibility needed by the current generator route.
-/
theorem onePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload_of_pointwiseCompatibilityCore
    (payload :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u} := by
  intro M _top _charted e c _hc q _hq _hselects
  exact payload e q

/--
The source-pointed transported local-inverse chart constructor payload supplies
the direct transported `chartAt` selector-generation payload.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_selectedByTransportedLocalInverseChartOnSourceCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected e hc with ⟨q, hqSource, hq⟩
  refine ⟨q, hqSource, ?_⟩
  exact hq.trans (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q)

/--
The forward inclusion into the transported local-inverse chart range supplies the
source-pointed constructor payload; the source point is provided by the
transported charted-space `mem_chart_source` field.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload_of_subsetTransportedLocalInverseChartRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases payload e hc with ⟨q, hq⟩
  refine ⟨q, ?_, hq.symm⟩
  have hSource :
      q ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q).source :=
    @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q
  simpa [← homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q, hq]
    using hSource

/--
Source points for ambient atlas charts plus source-conditioned range membership
recover the forward local-inverse range inclusion.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_chartSourcePoint_and_sourceNonemptySubsetTransportedLocalInverseChartRangeCore
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (sourceNonemptyRange :
      OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc
  exact sourceNonemptyRange e hc (sourcePoint hc)

/--
The direct transported source-pointed selector payload supplies the existing
transported `chartAt` generator formulation.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_selectedByTransportedChartAtOnSourceCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases selected e hc with ⟨q, _hqSource, hq⟩
  exact ⟨q, hq⟩

/--
The reverse inclusion from the selected ambient `chartAt` range into the
ambient atlas is part of the `ChartedSpace` API.
-/
theorem onePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload :
    OnePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload.{u} := by
  intro M _top _charted c hc
  rcases hc with ⟨q, rfl⟩
  exact @chart_mem_atlas ThreeManifoldModel M _ _ inferInstance q

/--
The source-existence and selector-choice facts together supply the
source-pointed selector-generation payload.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_chartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (selects :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted c hc
  rcases sourcePoint hc with ⟨q, hq⟩
  exact ⟨q, hq, selects hc hq⟩

/--
The three current source-pointed inputs already determine the direct transported
source-pointed selector-generation payload.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_chartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore_and_selectedSourceCompatibilityCore
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (selects :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u})
    (selectedCompat :
      OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases sourcePoint hc with ⟨q, hq⟩
  have hSelected :
      c = @ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance q :=
    selects hc hq
  refine ⟨q, hq, ?_⟩
  exact hSelected.trans (selectedCompat e hc hq hSelected)

/--
The source-pointed selector-generation payload supplies the source-existence
part.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointCorePayload_of_selectedByAmbientChartAtOnSourceCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u} := by
  intro M _top _charted c hc
  rcases selected hc with ⟨q, hq, _hqEq⟩
  exact ⟨q, hq⟩

/--
The source-pointed selector-generation payload supplies the set-theoretic
inclusion into the ambient selected-chart range.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} := by
  intro M _top _charted c hc
  rcases selected hc with ⟨q, _hqSource, hq⟩
  exact ⟨q, hq.symm⟩

/--
The current set-theoretic selector-inclusion payload already determines the
source-pointed form, because selected charts contain their selected point.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_subsetAmbientChartAtRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted c hc
  rcases payload hc with ⟨q, hq⟩
  refine ⟨q, ?_, hq.symm⟩
  simpa [hq] using @mem_chart_source ThreeManifoldModel M _ _ inferInstance q

/--
Ambient selector-inclusion is equivalently the source-pointed selector
generation invariant.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_iff_selectedByAmbientChartAtOnSourceCore :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} ↔
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_subsetAmbientChartAtRangeCore,
    onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore⟩

/--
The source-pointed selector-generation payload supplies the older ambient
generator formulation.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_selectedByAmbientChartAtOnSourceCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} := by
  intro M _top _charted c hc
  rcases selected hc with ⟨q, _hqSource, hq⟩
  exact ⟨q, hq⟩

/--
The older ambient generator formulation also supplies the source-pointed form,
because `ChartedSpace.mem_chart_source` provides the source membership.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_generatedByAmbientChartAtCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} := by
  intro M _top _charted c hc
  rcases generated hc with ⟨q, hq⟩
  refine ⟨q, ?_, hq⟩
  simp [hq]

/--
The ambient generator payload supplies the set-theoretic inclusion into the
ambient selected-chart range.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_of_generatedByAmbientChartAtCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} := by
  intro M _top _charted c hc
  rcases generated hc with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/--
The set-theoretic inclusion into the ambient selected-chart range supplies the
ambient generator payload.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_subsetAmbientChartAtRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} := by
  intro M _top _charted c hc
  rcases payload hc with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/--
Ambient generation by the selected-chart field is exactly the one-sided atlas
inclusion into the selected-chart range.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_iff_subsetAmbientChartAtRangeCore :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} ↔
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_of_generatedByAmbientChartAtCore,
    onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_subsetAmbientChartAtRangeCore⟩

/--
The one-sided selector-generation inclusion, together with the automatic
`chartAt`-range inclusion into the atlas, identifies the ambient atlas with the
selected-chart range.
-/
theorem onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload_of_subsetAmbientChartAtRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u} := by
  intro M _top _charted
  ext c
  constructor
  · intro hc
    exact payload hc
  · intro hc
    exact onePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload hc

/--
Atlas equality with the ambient selected-chart range supplies the one-sided
selector-generation inclusion.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload_of_eqAmbientChartAtRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} := by
  intro M _top _charted c hc
  simpa [payload (M := M)] using hc

/--
Atlas equality with the ambient selected-chart range supplies the current
ambient `chartAt` generator payload.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_eqAmbientChartAtRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} := by
  intro M _top _charted c hc
  have hRange :
      c ∈
        Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance) := by
    simpa [payload (M := M)] using hc
  rcases hRange with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/--
The ambient `chartAt` generator payload plus the automatic reverse inclusion
identifies the ambient atlas with the selected-chart range.
-/
theorem onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload_of_generatedByAmbientChartAtCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u} := by
  intro M _top _charted
  ext c
  constructor
  · intro hc
    rcases generated hc with ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · intro hc
    exact onePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload hc

/--
The previous ambient `chartAt` generator source is exactly equality of the
ambient atlas with the range of its selected-chart function; the reverse
inclusion is already provided by `ChartedSpace`.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_iff_eqAmbientChartAtRangeCore :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} ↔
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload_of_generatedByAmbientChartAtCore,
    onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_eqAmbientChartAtRangeCore⟩

/--
Ambient generation by the ambient `chartAt` selector, plus equality of the
ambient and transported selectors, supplies generation by the transported
`chartAt` selector.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_generatedByAmbientChartAtCore_and_chartAtCompatibilityCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases generated hc with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq, chartAtCompat e]

/--
Ambient generation by the ambient selector plus pointwise selected-chart
compatibility supplies generation by the transported selector.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_generatedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} :=
  onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_generatedByAmbientChartAtCore_and_chartAtCompatibilityCore
    generated
    (onePointRecognitionAmbientChartAtCompatibilityCorePayload_of_pointwiseCompatibilityCore
      chartAtCompat)

/--
The core transported-atlas inclusion supplies the recognition-shaped
one-sided transported-atlas inclusion.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_ambientAtlasSubsetTransportedAtlasCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  exact payload e

/--
If each ambient atlas chart is a transported `chartAt`, then it belongs to the
transported atlas.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_of_generatedByTransportedChartAtCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases generated e hc with ⟨q, hq⟩
  rw [hq]
  exact
    @chart_mem_atlas ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) q

/--
Conversely, membership in the transported atlas exposes the transported
`chartAt` generator point, because this transported atlas is generated by the
local-inverse chart constructor.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_ambientAtlasSubsetTransportedAtlasCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} := by
  intro M _top _charted e c hc
  have hTransported :
      c ∈
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e hc
  have hRange :
      c ∈ Set.range
        (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
    rwa [homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e] at hTransported
  rcases hRange with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  exact hq.symm.trans
    (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q)

/--
The one-sided transported-atlas core payload is equivalently the concrete
transported-`chartAt` generator source.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_iff_generatedByTransportedChartAtCore :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u} ↔
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_ambientAtlasSubsetTransportedAtlasCore,
    onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_of_generatedByTransportedChartAtCore⟩

/--
Forward inclusion into the transported atlas is the exact source needed for
forward inclusion into the transported local-inverse chart range, since the
transported atlas is definitionally that range.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_ambientAtlasSubsetTransportedAtlasCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc
  have hTransported :
      c ∈
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e hc
  rwa [homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
    e] at hTransported

/--
Forward inclusion into the local-inverse chart range is equivalently forward
inclusion into the transported atlas.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_of_subsetTransportedLocalInverseChartRangeCore
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  have hRange :
      c ∈ Set.range
        (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) :=
    payload e hc
  rwa [homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
    e]

/--
Reverse inclusion from the transported atlas into the ambient atlas supplies
the reverse transported local-inverse chart-range inclusion.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_transportedAtlasSubsetAmbientAtlasCore
    (payload :
      OnePointRecognitionTransportedAtlasSubsetAmbientAtlasCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  have hTransported :
      c ∈
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) := by
    rwa [homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e]
  exact payload e hTransported

/--
Pointwise ambient/transported selected-chart compatibility identifies each
explicit transported local-inverse chart with an ambient selected chart.
-/
theorem homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_ambientChartAt_range_of_pointwiseCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) (q : M) :
    homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e q ∈
      Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance) := by
  refine ⟨q, ?_⟩
  exact
    (chartAtCompat e q).trans
      (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q).symm

/--
Ambient atlas equality with the ambient selected-chart range plus pointwise
ambient/transported selected-chart compatibility supplies the reverse
transported local-inverse chart-range inclusion.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases hc with ⟨q, hq⟩
  have hAmbientRange :
      c ∈ Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance) := by
    rw [← hq]
    exact
      homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_ambientChartAt_range_of_pointwiseCompatibilityCore
        chartAtCompat e q
  have hEq := eqRange (M := M)
  rwa [hEq]

/--
Field-level selected-chart compatibility directly supplies the reverse
transported local-inverse chart-range inclusion.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_chartAtCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases hc with ⟨q, hq⟩
  rw [← hq]
  rw [homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_ambientChartAt_of_chartAtCompatibilityCore
    chartAtCompat e q]
  exact @chart_mem_atlas ThreeManifoldModel M _ _ inferInstance q

/--
Ambient atlas equality with the ambient selected-chart range plus field-level
selected-chart compatibility supplies the reverse transported local-inverse
chart-range inclusion without assuming pointwise compatibility separately.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqAmbientChartAtRangeCore_and_chartAtCompatibilityCore
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} :=
  onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
    eqRange
    (onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore
      chartAtCompat)

/--
Reverse inclusion from the local-inverse chart range into the ambient atlas is
equivalently reverse inclusion from the transported atlas.
-/
theorem onePointRecognitionTransportedAtlasSubsetAmbientAtlasCorePayload_of_rangeSubsetAmbientAtlasCore
    (payload :
      OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u}) :
    OnePointRecognitionTransportedAtlasSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  have hRange :
      c ∈ Set.range
        (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
    rwa [← homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e]
  exact payload e hRange

/--
The transported-atlas inclusion split recovers the existing local-inverse
range equality core.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_transportAtlasSubsetCore_and_transportedAtlasSubsetAmbientAtlasCore
    (ambientSubset :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u})
    (rangeSubset :
      OnePointRecognitionTransportedAtlasSubsetAmbientAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e
  exact Set.Subset.antisymm
    (onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_ambientAtlasSubsetTransportedAtlasCore
      ambientSubset e)
    (onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_transportedAtlasSubsetAmbientAtlasCore
      rangeSubset e)

/--
Core atlas equality supplies the forward inclusion of ambient atlas charts into
the transported local-inverse chart range.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_eqTransportedLocalInverseChartRangeCore
    (core :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e c hc
  have hEq := core e
  rw [hEq] at hc
  exact hc

/--
Core atlas equality supplies the reverse inclusion of the transported
local-inverse chart range into the ambient atlas.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqTransportedLocalInverseChartRangeCore
    (core :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  have hEq := core e
  rw [hEq]
  exact hc

/--
The two set-inclusion directions recover the core atlas equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subset_and_rangeSubset
    (ambientSubset :
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u})
    (rangeSubset :
      OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e
  exact Set.Subset.antisymm (ambientSubset e) (rangeSubset e)

/--
Source-pointed ambient selector generation plus pointwise `chartAt`
compatibility closes the forward inclusion side of the exact local-inverse
range equality; the remaining hypothesis is precisely the reverse range
inclusion.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore_and_rangeSubset
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u})
    (rangeSubset :
      OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subset_and_rangeSubset
    (onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
      selected chartAtCompat)
    rangeSubset

/--
Source-pointed ambient selector generation, ambient atlas equality with the
ambient selected-chart range, and pointwise ambient/transported `chartAt`
compatibility recover the exact transported local-inverse chart-range equality
without taking the reverse range inclusion as a separate input.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_eqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore_and_rangeSubset
    selected chartAtCompat
    (onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
      eqRange chartAtCompat)

/--
Source-pointed ambient selector generation, ambient atlas equality with the
ambient selected-chart range, and field-level selected-chart compatibility
recover the exact transported local-inverse chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_eqAmbientChartAtRangeCore_and_chartAtCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_eqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
    selected eqRange
    (onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore
      chartAtCompat)

/--
Pointwise ambient/transported `chartAt` compatibility alone supplies the
reverse transported local-inverse chart-range inclusion: every transported
local-inverse chart is identified with an ambient selected chart, and selected
ambient charts are atlas charts.
-/
theorem onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_chartAtPointwiseCompatibilityCore
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  intro M _top _charted e c hc
  rcases hc with ⟨q, hq⟩
  have hAmbientRange :
      c ∈ Set.range (@ChartedSpace.chartAt ThreeManifoldModel _ M _ inferInstance) := by
    rw [← hq]
    exact
      homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_mem_ambientChartAt_range_of_pointwiseCompatibilityCore
        chartAtCompat e q
  exact onePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload hAmbientRange

/--
Source-pointed ambient selector generation plus pointwise ambient/transported
selected-chart compatibility recovers the exact transported local-inverse
chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore_and_rangeSubset
    selected chartAtCompat
    (onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_chartAtPointwiseCompatibilityCore
      chartAtCompat)

/--
Ambient generation by the selected `chartAt` field plus pointwise
ambient/transported selected-chart compatibility recovers the exact transported
local-inverse chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_generatedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    (onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_generatedByAmbientChartAtCore
      generated)
    chartAtCompat

/--
The one-sided ambient atlas inclusion into the ambient `chartAt` range plus
pointwise selected-chart compatibility recovers the exact transported
local-inverse chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subsetAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore
    (subsetRange :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e
  refine Set.Subset.antisymm ?_ ?_
  · intro c hc
    rcases subsetRange hc with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    exact
      (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt e q).trans
        ((chartAtCompat e q).symm.trans hq)
  · exact
      onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_chartAtPointwiseCompatibilityCore
        chartAtCompat e

/--
Field-level selected-chart compatibility supplies the exact range equality
route that previously used pointwise selected-chart compatibility.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtCompatibilityCore
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore
    selected
    (onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore
      chartAtCompat)

/--
Ambient generation by the selected `chartAt` field plus field-level
selected-chart compatibility recovers the exact transported local-inverse
chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_generatedByAmbientChartAtCore_and_chartAtCompatibilityCore
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} :=
  onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_generatedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore
    generated
    (onePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload_of_chartAtCompatibilityCore
      chartAtCompat)

/--
The one-sided ambient atlas inclusion into the ambient `chartAt` range plus
field-level selected-chart compatibility recovers the exact transported
local-inverse chart-range equality.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subsetAmbientChartAtRangeCore_and_chartAtCompatibilityCore
    (subsetRange :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} := by
  intro M _top _charted e
  refine Set.Subset.antisymm ?_ ?_
  · intro c hc
    rcases subsetRange hc with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    exact
      (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_ambientChartAt_of_chartAtCompatibilityCore
        chartAtCompat e q).trans hq
  · intro c hc
    rcases hc with ⟨q, hq⟩
    rw [← hq]
    rw [homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_ambientChartAt_of_chartAtCompatibilityCore
      chartAtCompat e q]
    exact @chart_mem_atlas ThreeManifoldModel M _ _ inferInstance q

/--
The core atlas-range equality is exactly the pair of its two inclusion
directions.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_iff_subset_and_rangeSubset :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} ↔
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} ∧
        OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} := by
  constructor
  · intro core
    exact
      ⟨onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_eqTransportedLocalInverseChartRangeCore
          core,
        onePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload_of_eqTransportedLocalInverseChartRangeCore
          core⟩
  · intro h
    exact
      onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subset_and_rangeSubset
        h.1 h.2

/--
The constructor-level local-inverse generator source supplies the accepted
transported-`chartAt` generator payload.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload_of_generatedByTransportedLocalInverseChart
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  rcases generated e hc with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq, homeomorphToOnePoint_threeSpace_transportedLocalInverseChart_eq_chartAt]

/--
Atlas-field equality with the transported local-inverse generator range
supplies the pointwise constructor-level generator payload.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload_of_eqTransportedLocalInverseChartRange
    (eqRange :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  have hRange :
      c ∈ Set.range
        (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e) := by
    simpa [eqRange e] using hc
  rcases hRange with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/--
Full charted-space compatibility supplies the exact local-inverse generator
range equality for the ambient atlas field.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  have hEq :
      _charted = homeomorphToOnePoint_threeSpace_smoothChartedSpace e :=
    compat e
  change
    @atlas ThreeManifoldModel _ M _ _charted =
      Set.range (homeomorphToOnePoint_threeSpace_transportedLocalInverseChart e)
  rw [hEq]
  exact
    homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e

/--
The older ambient-atlas compatibility payload supplies the same field
comparison with the transported atlas definition unfolded.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload_of_ambientAtlasCompatibility
    (compat :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  rw [compat e]
  exact
    homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e

/--
Conversely, the range formulation recovers ambient-atlas compatibility because
the transported atlas is definitionally that local-inverse chart range.
-/
theorem onePointRecognitionAmbientAtlasCompatibilityPayload_of_eqTransportedLocalInverseChartRange
    (eqRange :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u}) :
    OnePointRecognitionAmbientAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  rw [eqRange e]
  exact
    (homeomorphToOnePoint_threeSpace_smoothChartedSpace_atlas_eq_transportedLocalInverseChart_range
      e).symm

/--
The transported local-inverse range formulation is exactly the existing
ambient-atlas compatibility payload with the transported atlas unfolded.
-/
theorem onePointRecognitionAmbientAtlasCompatibilityPayload_iff_eqTransportedLocalInverseChartRange :
    OnePointRecognitionAmbientAtlasCompatibilityPayload.{u} ↔
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload_of_ambientAtlasCompatibility,
    onePointRecognitionAmbientAtlasCompatibilityPayload_of_eqTransportedLocalInverseChartRange⟩

/--
Full charted-space compatibility also supplies the selected-chart comparison.
-/
theorem onePointRecognitionAmbientChartAtCompatibilityPayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartAtCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  have hEq :
      _charted = homeomorphToOnePoint_threeSpace_smoothChartedSpace e :=
    compat e
  change
    @ChartedSpace.chartAt ThreeManifoldModel _ M _ _charted =
      @ChartedSpace.chartAt ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
  rw [hEq]

/--
`ChartedSpace.ext` exposes the exact data needed to identify an arbitrary
ambient charted-space instance with the transported one: both the atlas and
the chosen `chartAt` function must agree.
-/
theorem onePointRecognitionAmbientChartedSpaceCompatibilityPayload_of_atlas_and_chartAtCompatibility
    (atlasCompat :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  have hAtlas :
      @atlas ThreeManifoldModel _ M _ _charted =
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    atlasCompat e
  have hChartAt :
      @ChartedSpace.chartAt ThreeManifoldModel _ M _ _charted =
        @ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    chartAtCompat e
  exact ChartedSpace.ext hAtlas hChartAt

/--
Thus the stronger charted-space compatibility route is precisely the pair of
field comparisons required by `ChartedSpace.ext`; one-point recognition alone
does not choose the arbitrary ambient `chartAt` field.
-/
theorem onePointRecognitionAmbientChartedSpaceCompatibilityPayload_iff_atlas_and_chartAtCompatibility :
    OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u} ↔
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u} ∧
        OnePointRecognitionAmbientChartAtCompatibilityPayload.{u} := by
  constructor
  · intro compat
    exact
      ⟨onePointRecognitionAmbientAtlasCompatibilityPayload_of_chartedSpaceCompatibility
          compat,
        onePointRecognitionAmbientChartAtCompatibilityPayload_of_chartedSpaceCompatibility
          compat⟩
  · intro h
    exact
      onePointRecognitionAmbientChartedSpaceCompatibilityPayload_of_atlas_and_chartAtCompatibility
        h.1 h.2

/--
If the selected-chart comparison is unavailable, the stronger universal
charted-space compatibility payload is unavailable, even before using it to
derive the atlas-level package bridge.
-/
theorem onePointRecognitionAmbientChartedSpaceCompatibilityPayload_currently_blocked_at_chartAtCompatibility
    (chartAtUnavailable :
      OnePointRecognitionAmbientChartAtCompatibilityPayload.{u} → False) :
    OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u} →
      False := by
  intro compat
  exact chartAtUnavailable
    (onePointRecognitionAmbientChartAtCompatibilityPayload_of_chartedSpaceCompatibility
      compat)

/--
The existing `SmoothabilityOnePointRecognition` surface owns the atlas
comparison for the charted-space witness it constructs: when the ambient
charted-space instance is the transported one-point compactification atlas, the
comparison is definitional.
-/
theorem onePointRecognitionAmbientAtlasCompatibility_on_transportedChartedSpace
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    letI : ChartedSpace ThreeManifoldModel M :=
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e
    atlas ThreeManifoldModel M =
      @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) := by
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  rfl

/--
The charted-space equality behind the atlas comparison is also definitional
for the transported one-point charted-space witness.  The universal ambient
payload remains stronger because it asks for this equality for an arbitrary
ambient `[ChartedSpace ThreeManifoldModel M]`.
-/
theorem onePointRecognitionAmbientChartedSpaceCompatibility_on_transportedChartedSpace
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    letI : ChartedSpace ThreeManifoldModel M :=
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e
    (inferInstance : ChartedSpace ThreeManifoldModel M) =
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e := by
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  rfl

/--
The transported one-point compactification charted space already carries the
surgery-layer manifold evidence.
-/
def OnePointRecognitionTransportedSmoothabilityBridgePayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
          ThreeManifoldModelWithCorners 1 M inferInstance
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Existing one-point smoothability closes the transported-charted-space
smoothability bridge payload.
-/
theorem onePointRecognitionTransportedSmoothabilityBridgePayload :
    OnePointRecognitionTransportedSmoothabilityBridgePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e
  exact homeomorphToOnePoint_threeSpace_surgeryModel_isManifold e

/--
Transported-charted-space bridge statement: one-point recognition supplies a
specific charted-space witness and the surgery-layer manifold evidence for
that witness, rather than evidence for an arbitrary ambient charted-space
instance.
-/
def OnePointRecognitionTransportedChartedBridgeStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∃ charted : ChartedSpace ThreeManifoldModel M,
          letI : ChartedSpace ThreeManifoldModel M := charted
          IsManifold ThreeManifoldModelWithCorners 1 M

/--
The existing one-point recognition surface proves the transported-charted-space
bridge directly.
-/
theorem onePointRecognitionTransportedChartedBridgeStatement :
    OnePointRecognitionTransportedChartedBridgeStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases h with ⟨e⟩
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact homeomorphToOnePoint_threeSpace_surgeryModel_isManifold e

/--
The one-point recognition route supplies the core transported bridge statement
now exposed by `Poincare.Smoothability`.
-/
theorem smoothabilityTransportedBridgeStatement_of_onePointRecognition :
    SmoothabilityTransportedBridgeStatement.{u} := by
  intro M _top _t2 _simple _compact h
  exact onePointRecognitionTransportedChartedBridgeStatement h

/--
The one-point recognition route supplies the additive transported bridge
package field.
-/
theorem smoothabilityTransportedBridgePackageField_of_onePointRecognition :
    SmoothabilityTransportedBridgePackageField.{u} where
  transportedBridge :=
    smoothabilityTransportedBridgeStatement_of_onePointRecognition

/--
The one-point recognition route also supplies the transported `C∞`
smooth-manifold statement: the produced charted-space witness is the transported
one-point compactification smooth atlas.
-/
theorem smoothabilityTransportedSmoothManifoldStatement_of_onePointRecognition :
    SmoothabilityTransportedSmoothManifoldStatement.{u} := by
  intro M _top _t2 _simple _compact h
  rcases h with ⟨e⟩
  let charted : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  exact homeomorphToOnePoint_threeSpace_smoothManifold e

/--
The one-point recognition route supplies the transported analogue of the
`SmoothabilityPackage.smoothManifold` field.
-/
theorem smoothabilityTransportedSmoothManifoldPackageField_of_onePointRecognition :
    SmoothabilityTransportedSmoothManifoldPackageField.{u} where
  transportedSmoothManifold :=
    smoothabilityTransportedSmoothManifoldStatement_of_onePointRecognition

/--
The exact remaining comparison datum: the transported one-point
`IsManifold` evidence must be usable for the ambient charted-space instance
already in scope.
-/
def OnePointRecognitionAmbientChartedSpaceComparisonPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
          ThreeManifoldModelWithCorners 1 M inferInstance
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
        IsManifold ThreeManifoldModelWithCorners 1 M

/--
The theorem-level form of the remaining charted-space comparison: transfer the
transported one-point `IsManifold` evidence to the ambient charted-space
instance already in scope.
-/
def OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem : Prop :=
  OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u}

/-- The named transfer theorem is definitionally the current comparison payload. -/
theorem onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_eq :
    OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} =
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} :=
  rfl

/--
The mathlib-native sufficient condition for that transfer: every ambient chart
is already in the maximal smooth atlas determined by the transported one-point
charted space.
-/
def OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        atlas ThreeManifoldModel M ⊆
          @IsManifold.maximalAtlas ℝ _ ThreeManifoldModel _ _
            ThreeManifoldModel _ ThreeManifoldModelWithCorners 1 M
            inferInstance
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Pointwise form of the transported maximal-atlas source datum: each ambient
chart is already a chart in the transported smooth maximal atlas.
-/
def OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            c ∈
              @IsManifold.maximalAtlas ℝ _ ThreeManifoldModel _ _
                ThreeManifoldModel _ ThreeManifoldModelWithCorners 1 M
                inferInstance
                (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
The pointwise chart-membership datum supplies the set-containment payload used
to transfer ambient charts into the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload_of_chartInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  exact payload e hc

/--
Conversely, the set-containment payload is exactly the pointwise chart
membership statement.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_atlasInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  exact payload e hc

/--
Thus the transported maximal-atlas route is blocked precisely at the local
chart-membership assertion.
-/
theorem onePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload_currently_blocked_at_chartInTransportedMaximalAtlas
    (chartMembershipUnavailable :
      OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u} →
      False := by
  intro payload
  exact chartMembershipUnavailable
    (onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_atlasInTransportedMaximalAtlas
      payload)

/--
The chart-level source of the pointwise maximal-atlas membership: every
ambient chart is compatible, in both directions, with every chart from the
transported one-point atlas.
-/
def OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c d : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
          d ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            c.symm ≫ₕ d ∈
              contDiffGroupoid 1 ThreeManifoldModelWithCorners ∧
            d.symm ≫ₕ c ∈
              contDiffGroupoid 1 ThreeManifoldModelWithCorners

/--
One directional form of the chart-level cross-atlas source.  The reverse
transition is its inverse, so this is the first genuinely unavailable local
transition theorem.
-/
def OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c d : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
          d ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            c.symm ≫ₕ d ∈
              contDiffGroupoid 1 ThreeManifoldModelWithCorners

/--
Local restricted-transition form of the forward cross-atlas source.  This is
the exact datum consumed by `StructureGroupoid.locality` for the transition
from an ambient chart to a transported one-point chart.
-/
def OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c d : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
          d ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ x ∈ (c.symm ≫ₕ d).source,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  (c.symm ≫ₕ d).restr s ∈
                    contDiffGroupoid 1 ThreeManifoldModelWithCorners

/--
Primitive local normal-form source for the local forward cross-atlas theorem:
near each point of an ambient-to-transported transition, the restricted
transition is the same open partial homeomorphism as a transition from a
transported one-point chart to the transported target chart.
-/
def OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c d : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
          d ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ x ∈ (c.symm ≫ₕ d).source,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  ∃ t : OpenPartialHomeomorph M ThreeManifoldModel,
                    t ∈ @atlas ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) ∧
                    (c.symm ≫ₕ d).restr s =
                      (t.symm ≫ₕ d).restr s

/--
Primitive inverse-chart normal form underneath the local transition model:
near each model point in the target of an ambient chart, the ambient chart
inverse is literally a restriction of a transported one-point chart inverse.
-/
def OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ x ∈ c.target,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  ∃ t : OpenPartialHomeomorph M ThreeManifoldModel,
                    t ∈ @atlas ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) ∧
                    c.symm.restr s = t.symm.restr s

/--
Sharper inverse-chart source underneath the inverse-atlas normal form: the
transported one-point chart is no longer arbitrary, but the canonical
transported `chartAt` at the ambient inverse point.
-/
def OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ x ∈ c.target,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  c.symm.restr s =
                    (@ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      (c.symm x)).symm.restr s

/--
Weaker source under the canonical transported `chartAt` inverse model: for
the local transition argument, the restricted inverse charts only need to be
equivalent on their source.  Structure-groupoid membership ignores the
irrelevant values outside the source via `StructureGroupoid.mem_of_eqOnSource`.
-/
def OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ x ∈ c.target,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  c.symm.restr s ≈
                    (@ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      (c.symm x)).symm.restr s

/--
Unfolded source-equivalence source for the canonical transported `chartAt`
inverse model.  Since the inverse charts have source equal to the target of the
original charts, the missing local restriction identity is exactly local target
equality together with pointwise equality of the inverse maps on that target.
-/
def OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ x ∈ c.target,
              ∃ s : Set ThreeManifoldModel,
                IsOpen s ∧ x ∈ s ∧
                  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                    @ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      (c.symm x)
                  c.target ∩ s = t.target ∩ s ∧
                    Set.EqOn c.symm t.symm (c.target ∩ s)

/--
Manifold-side local chart-germ source underneath the model-side target/inverse
identity.  For a single ambient chart `c` and the transported `chartAt` at
`c.symm x`, it asks only that the two forward charts have the same local source
inside an open neighborhood of `c.symm x` and agree there.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ x ∈ c.target,
              ∃ u : Set M,
                IsOpen u ∧ c.symm x ∈ u ∧
                  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                    @ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      (c.symm x)
                  c.source ∩ u = t.source ∩ u ∧
                    Set.EqOn c t (c.source ∩ u)

/--
Local restriction-equality source underneath the manifold-side chart-germ
payload.  It is still local and pointwise: for each source point of an ambient
atlas chart, the restricted chart agrees with the transported `chartAt` selected
at that same point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              ∃ u : Set M,
                IsOpen u ∧ p ∈ u ∧
                  c.restr u =
                    (@ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      p).restr u

/--
Weaker local restriction-germ source: the restricted ambient chart and
transported `chartAt` only need to be equivalent on their source.  This avoids
the total-map equality required by equality of open partial homeomorphisms.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              ∃ u : Set M,
                IsOpen u ∧ p ∈ u ∧
                  c.restr u ≈
                    (@ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      p).restr u

/--
Pointwise local chart-germ source below restricted-chart source-equivalence.
The source equality part of `EqOnSource` is obtained by shrinking to the
intersection of the two chart sources; the only remaining local datum is that
the forward chart maps agree near the source point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              ∃ u : Set M,
                IsOpen u ∧ p ∈ u ∧
                  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                    @ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      p
                  Set.EqOn c t (c.source ∩ u)

/--
Source-restricted chart-germ source below the open-neighborhood formulation:
the ambient chart and transported `chartAt` agree eventually in the
neighborhood filter within the ambient chart source at the source point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ y in nhdsWithin p c.source, c y = t y

/--
Conditional source-germ chart-map source below full source-restricted equality:
near the ambient source point, the transported chart map must agree with the
ambient chart map only at points that lie in the transported `chartAt` source.
This is the exact local datum needed both at the source point and after pulling
back model points by the ambient inverse chart.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ y in nhdsWithin p c.source,
                y ∈ t.source → t y = c y

/--
Common-source chart-germ source below the source-restricted formulation:
the ambient chart and transported `chartAt` are compared only on the common
source where both chart maps are meaningful.  This is enough because the
transported `chartAt` source is an open neighborhood of the source point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y

/--
First source datum below common-source chart-germ equality: every ambient atlas
chart must actually be a chart in the transported one-point atlas.  This is
strictly weaker than equality of the two atlases and is the membership fact
needed before transported-atlas `chartAt` locality can be applied.
-/
def OnePointRecognitionAmbientChartInTransportedAtlasPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            c ∈ @atlas ThreeManifoldModel _ M _
              (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)

/--
Second source datum below common-source chart-germ equality: inside the
transported one-point atlas itself, an atlas chart and the transported `chartAt`
selected at a point of its source agree as germs on their common source.  This
isolates the chart-selection/locality theorem not provided by ordinary smooth
atlas compatibility.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y

/--
Model-side transition-identity source for the internal transported-atlas
`chartAt` germ theorem.  It asks that the coordinate change from a transported
atlas chart to the transported `chartAt` selected at a point of its source is
locally the identity on its actual source.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z

/--
Chart-map source below the internal transported-atlas transition identity: on
the actual source of the coordinate transition, the transported `chartAt` map
agrees with the transported atlas chart map after applying `c.symm`.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source,
                t (c.symm z) = c (c.symm z)

/--
Target-membership source below internal transported-atlas transition identity:
on the actual source of the coordinate transition, model points eventually lie
in the selected transported `chartAt` target.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source,
                z ∈ t.target

/--
Inverse-map source below internal transported-atlas transition identity: after
restricting the actual transition source to the selected transported target,
the inverse maps of the transported atlas chart and selected `chartAt` agree.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                c.symm z = t.symm z

/--
Point-target source below internal transported-atlas transition target
membership: the transported atlas chart value at the represented point lies in
the selected transported `chartAt` target.
-/
def OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              c p ∈ t.target

/--
Selected-target source-inclusion source below internal transported-atlas
inverse equality: after restricting the actual transition source to the
selected target, the selected transported inverse lands in the transported
atlas chart source.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                t.symm z ∈ c.source

/--
Selected-target chart-map source below internal transported-atlas inverse
equality: on the selected-target restriction of the actual transition source,
the transported atlas chart sends the selected transported inverse back to the
model point, once the source-membership fact has been isolated.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                t.symm z ∈ c.source → c (t.symm z) = z

/--
Pointwise chart equality source below transported-atlas point target
membership: at each source point, a transported atlas chart and the selected
transported `chartAt` have the same coordinate value.
-/
def OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              c p = t p

/--
Target-preimage chart-map source below transported-atlas selected-target
chart-map equality: on the transported atlas chart target, whenever the inverse
point lies in the selected `chartAt` source, the two chart maps agree there.
-/
def OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) c.target,
                c.symm z ∈ t.source → t (c.symm z) = c (c.symm z)

/--
Source-side chart-map choice compatibility below the target-preimage
right-inverse source: near a point of a transported atlas chart, the selected
transported `chartAt` agrees with that chart at every point where both are
defined.  This removes the inverse-chart wrapper from the remaining local
chartAt-choice obligation.
-/
def OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ y in nhdsWithin p c.source,
                y ∈ t.source → t y = c y

/--
Explicit chartAt-choice source below source-side chart-map compatibility:
inside the transported atlas, the selected transported `chartAt` at `p` is
the transported atlas chart `c` whenever `p` lies in `c.source`.

This isolates the genuine chart-selection datum; ordinary atlas membership
only gives that both charts belong to the atlas, not that the charted-space
field `chartAt` chooses the arbitrary atlas chart `c`.
-/
def OnePointRecognitionTransportedAtlasChartAtChoosesAtlasChartPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p = c

/--
Target-preimage right-inverse source below transported-atlas chart-map
agreement: on the transported atlas chart target, whenever the inverse point
lies in the selected `chartAt` source, the selected transported chart sends it
back to the model point.
-/
def OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) c.target,
                c.symm z ∈ t.source → t (c.symm z) = z

/--
Common-target transported inverse convergence source below selected-target
source inclusion: along the common model target, the selected transported
inverse tends back to the represented source point.
-/
def OnePointRecognitionTransportedAtlasChartAtCommonTargetSymmTendstoPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ @atlas ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target))
                (nhds p)

/--
Atlas equality supplies the weaker ambient-chart membership source used by the
new transported-atlas chart-germ frontier.
-/
theorem onePointRecognitionAmbientChartInTransportedAtlasPayload_of_ambientAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  have hAtlas :
      atlas ThreeManifoldModel M =
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e
  simpa [hAtlas] using hc

/--
The atlas-subset payload is exactly the pointwise ambient-chart membership
payload, unfolded as a set inclusion.
-/
theorem onePointRecognitionAmbientChartInTransportedAtlasPayload_of_ambientAtlasSubsetTransportedAtlas
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  exact payload e hc

/--
Conversely, pointwise ambient-chart membership is the one-sided atlas
inclusion.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_chartInTransportedAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  exact payload e hc

/--
The current chart-membership frontier is equivalent to the one-sided
ambient-atlas inclusion into the transported atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedAtlasPayload_iff_ambientAtlasSubsetTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u} ↔
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} :=
  ⟨onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_chartInTransportedAtlas,
    onePointRecognitionAmbientChartInTransportedAtlasPayload_of_ambientAtlasSubsetTransportedAtlas⟩

/--
The pointwise ambient-chart membership frontier is blocked exactly at the
one-sided ambient-atlas inclusion into the transported atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedAtlasPayload_currently_blocked_at_ambientAtlasSubsetTransportedAtlas
    (subsetUnavailable :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u} →
      False := by
  intro payload
  exact subsetUnavailable
    (onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_chartInTransportedAtlas
      payload)

/--
The ambient-chart-in-transported-atlas source plus the internal transported-atlas
`chartAt` germ theorem recover the accepted common-source chart-germ payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_chartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (transportedAtlasChartAtCommonSourceGermEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hTransported :
      c ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    chartInTransportedAtlas e hc
  simpa [t] using
    transportedAtlasChartAtCommonSourceGermEq e hTransported p hp

/--
Atlas equality plus the internal transported-atlas `chartAt` germ theorem also
recover the accepted common-source chart-germ payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_ambientAtlasCompatibility_and_transportedAtlasChartAtCommonSourceGermEq
    (atlasCompatibility :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u})
    (transportedAtlasChartAtCommonSourceGermEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_chartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq
    (onePointRecognitionAmbientChartInTransportedAtlasPayload_of_ambientAtlasCompatibility
      atlasCompatibility)
    transportedAtlasChartAtCommonSourceGermEq

/--
Internal transported-atlas chart-map agreement on the actual transition source
supplies the transported-atlas transition identity.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_transitionChartMapEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hMapEq :
      ∀ᶠ z in nhdsWithin (c p) φ.source,
        t (c.symm z) = c (c.symm z) := by
    simpa [t, φ] using payload e hc p hp
  filter_upwards [hMapEq, eventually_mem_nhdsWithin] with z hEq hzSource
  have hzTarget : z ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.1
  calc
    φ z = t (c.symm z) := by
      dsimp [φ]
    _ = c (c.symm z) := hEq
    _ = z := c.right_inv hzTarget

/--
Internal transported-atlas transition identity is enough for the chart-map
agreement source: on the actual coordinate-transition source, the ambient chart
right-inverse rewrites `c (c.symm z)` back to `z`.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload_of_transitionId
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hTransition :
      ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z := by
    simpa [t, φ] using payload e hc p hp
  filter_upwards [hTransition, eventually_mem_nhdsWithin] with z hId hzSource
  have hzTarget : z ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.1
  calc
    t (c.symm z) = φ z := by
      dsimp [φ]
    _ = z := hId
    _ = c (c.symm z) := (c.right_inv hzTarget).symm

/--
Internal transported-atlas target membership on the actual transition source
and inverse-map equality on the target-restricted transition source supply the
internal coordinate-transition identity.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_targetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hTargetMem :
      ∀ᶠ z in nhdsWithin (c p) φ.source, z ∈ t.target := by
    simpa [t, φ] using targetMem e hc p hp
  have hInvEq :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        c.symm z = t.symm z := by
    simpa [t, φ] using invEqOnTarget e hc p hp
  have hRestrict : φ.source ∩ t.target ∈ nhdsWithin (c p) φ.source := by
    filter_upwards [eventually_mem_nhdsWithin, hTargetMem] with z hzSource hzTarget
    exact ⟨hzSource, hzTarget⟩
  have hInvEqOnSource :
      ∀ᶠ z in nhdsWithin (c p) φ.source, c.symm z = t.symm z :=
    hInvEq.filter_mono (nhdsWithin_le_iff.mpr hRestrict)
  filter_upwards [hTargetMem, hInvEqOnSource] with z hzTarget hzInvEq
  calc
    φ z = t (c.symm z) := by
      dsimp [φ]
    _ = t (t.symm z) := by rw [hzInvEq]
    _ = z := t.right_inv hzTarget

/--
Point target membership supplies internal transported-atlas target membership on
the actual transition source by openness of the selected transported chart
target.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
    (payload :
      OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPoint : c p ∈ t.target := by
    simpa [t] using payload e hc p hp
  have hTarget : ∀ᶠ z in nhds (c p), z ∈ t.target :=
    t.open_target.mem_nhds hPoint
  exact hTarget.filter_mono nhdsWithin_le_nhds

/--
Selected-target source inclusion and conditional chart-map equality supply the
internal transported-atlas inverse-map equality on the selected-target
restriction of the actual transition source.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload_of_targetSymmSourceInclusion_and_targetSymmChartMapEqOnSource
    (sourceInclusion :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u})
    (chartMapEqOnSource :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hSource :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ c.source := by
    simpa [t, φ] using sourceInclusion e hc p hp
  have hChart :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ c.source → c (t.symm z) = z := by
    simpa [t, φ] using chartMapEqOnSource e hc p hp
  filter_upwards [hSource, hChart, eventually_mem_nhdsWithin] with z hzSource hzChart hzCommon
  have hzTransitionSource : z ∈ φ.source := hzCommon.1
  have hzTarget : z ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hzTransitionSource
    exact hzTransitionSource.1
  have hzSymmSource : c.symm z ∈ c.source := c.map_target hzTarget
  exact c.injOn hzSymmSource hzSource
    ((c.right_inv hzTarget).trans (hzChart hzSource).symm)

/--
Pointwise equality of the transported atlas chart and selected transported
`chartAt` at the represented source point supplies point target membership.
-/
theorem onePointRecognitionTransportedAtlasChartAtPointTargetMemPayload_of_pointChartEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hPointEq : c p = t p := by
    simpa [t] using payload e hc p hp
  simpa [hPointEq] using t.map_source hpt

/--
Pointwise chart equality supplies common-target transported inverse convergence
using continuity of the selected transported inverse chart.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonTargetSymmTendstoPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hPoint : c p = t p := by
    simpa [t] using payload e hc p hp
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hcpTarget : c p ∈ t.target := by
    rw [hPoint]
    exact t.map_source hpt
  have hSymm : t.symm (c p) = p := by
    rw [hPoint]
    exact t.left_inv hpt
  have hTendstoFull :
      Filter.Tendsto t.symm (nhds (c p)) (nhds p) := by
    simpa [hSymm] using (t.continuousAt_symm hcpTarget).tendsto
  exact hTendstoFull.mono_left nhdsWithin_le_nhds

/--
Pointwise chart equality supplies selected-target source inclusion by first
giving convergence of the selected transported inverse back to the source
point.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_pointChartEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hTendsto :
      Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target))
        (nhds p) := by
    simpa [t] using
      onePointRecognitionTransportedAtlasChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
        payload e hc p hp
  have hSource : ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
      t.symm z ∈ c.source :=
    hTendsto (c.open_source.mem_nhds hp)
  exact hSource.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
Target-preimage chart-map agreement plus pointwise chart equality supplies
selected-target conditional chart-map agreement after the transported inverse.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (pointChartEq :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hTargetPreimage :
      ∀ᶠ w in nhdsWithin (c p) c.target,
        c.symm w ∈ t.source → t (c.symm w) = c (c.symm w) := by
    simpa [t] using targetPreimageChartMapEqOnSource e hc p hp
  rw [eventually_nhdsWithin_iff] at hTargetPreimage
  have hTendsto :
      Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target))
        (nhds p) := by
    simpa [t] using
      onePointRecognitionTransportedAtlasChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
        pointChartEq e hc p hp
  have hChartTendsto :
      Filter.Tendsto (fun z => c (t.symm z))
        (nhdsWithin (c p) (c.target ∩ t.target)) (nhds (c p)) := by
    simpa [Function.comp_def] using (c.continuousAt hp).tendsto.comp hTendsto
  have hPull :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) ∈ c.target →
          c.symm (c (t.symm z)) ∈ t.source →
            t (c.symm (c (t.symm z))) = c (c.symm (c (t.symm z))) :=
    hChartTendsto.eventually hTargetPreimage
  have hCommon :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source → c (t.symm z) = z := by
    filter_upwards [hPull, eventually_mem_nhdsWithin] with z hzPull hzCommon hzAmbientSource
    have hLeft : c.symm (c (t.symm z)) = t.symm z :=
      c.left_inv hzAmbientSource
    have hzChartTarget : c (t.symm z) ∈ c.target :=
      c.map_source hzAmbientSource
    have hzTransportedSource : c.symm (c (t.symm z)) ∈ t.source := by
      rw [hLeft]
      exact t.map_target hzCommon.2
    have hEq := hzPull hzChartTarget hzTransportedSource
    have hChartEq : c (t.symm z) = t (t.symm z) := by
      simpa [hLeft] using hEq.symm
    exact hChartEq.trans (t.right_inv hzCommon.2)
  exact hCommon.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
Target-preimage chart-map equality already determines the selected
transported chart value at the represented source point.
-/
theorem onePointRecognitionTransportedAtlasChartAtPointChartEqPayload_of_targetPreimageChartMapEqOnSource
    (payload :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hMap :
      ∀ᶠ z in nhdsWithin (c p) c.target,
        c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) := by
    simpa [t] using payload e hc p hp
  have hcpTarget : c p ∈ c.target := c.map_source hp
  have hAt :
      c.symm (c p) ∈ t.source →
        t (c.symm (c p)) = c (c.symm (c p)) :=
    hMap.self_of_nhdsWithin hcpTarget
  have hSymm : c.symm (c p) = p := c.left_inv hp
  have hSymmSource : c.symm (c p) ∈ t.source := by
    simpa [hSymm] using hpt
  calc
    c p = c (c.symm (c p)) := (c.right_inv hcpTarget).symm
    _ = t (c.symm (c p)) := (hAt hSymmSource).symm
    _ = t p := by rw [hSymm]

/--
The target-preimage right-inverse source supplies target-preimage chart-map
agreement by rewriting the transported atlas chart right-inverse on its target.
-/
theorem onePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload_of_targetPreimageRightInv
    (payload :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hRightInv :
      ∀ᶠ z in nhdsWithin (c p) c.target,
        c.symm z ∈ t.source → t (c.symm z) = z := by
    simpa [t] using payload e hc p hp
  filter_upwards [hRightInv, eventually_mem_nhdsWithin] with z hzRightInv hzTarget hzSource
  exact (hzRightInv hzSource).trans (c.right_inv hzTarget).symm

/--
If the charted-space selector `chartAt p` chooses the transported atlas chart
`c`, then the source-side conditional chart-map equality is immediate.
-/
theorem onePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload_of_chartAtChoosesAtlasChart
    (payload :
      OnePointRecognitionTransportedAtlasChartAtChoosesAtlasChartPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hChoice : t = c := by
    simpa [t] using payload e hc p hp
  filter_upwards [] with y
  intro _hyTransportedSource
  exact congrArg (fun f : OpenPartialHomeomorph M ThreeManifoldModel => f y) hChoice

/--
The source-side conditional chart-map equality supplies the common-source germ
equality by restricting from the ambient source to the common chart source.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_sourceChartMapEqOnTransportedSource
    (payload :
      OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSourceMap :
      ∀ᶠ y in nhdsWithin p c.source,
        y ∈ t.source → t y = c y := by
    simpa [t] using payload e hc p hp
  have hCommonMap :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source),
        y ∈ t.source → t y = c y :=
    hSourceMap.filter_mono
      (nhdsWithin_mono _ Set.inter_subset_left)
  filter_upwards [hCommonMap, eventually_mem_nhdsWithin] with y hEq hySource
  exact (hEq hySource.2).symm

/--
The source-side conditional chart-map equality is enough for the
target-preimage right-inverse source, via the existing common-source germ
route.
-/
theorem onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_sourceChartMapEqOnTransportedSource
    (payload :
      OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSourceMap :
      ∀ᶠ y in nhdsWithin p c.source,
        y ∈ t.source → t y = c y := by
    simpa [t] using payload e hc p hp
  have hOnPreimage :
      ∀ᶠ z in nhdsWithin (c p) (c.symm ⁻¹' c.source),
        c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) :=
    (c.eventually_nhdsWithin'
        (fun y => y ∈ t.source → t y = c y) hp).mpr
      hSourceMap
  have hTargetSubset : c.target ⊆ c.symm ⁻¹' c.source := by
    intro z hzTarget
    exact c.map_target hzTarget
  have hOnTarget :
      ∀ᶠ z in nhdsWithin (c p) c.target,
        c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) :=
    hOnPreimage.filter_mono
      (nhdsWithin_mono _ hTargetSubset)
  filter_upwards [hOnTarget, eventually_mem_nhdsWithin] with
      z hzMap hzTarget hzSource
  exact (hzMap hzSource).trans (c.right_inv hzTarget)

/--
Internal transported-atlas common-source chart-germ equality supplies the
target-preimage right-inverse source by pulling the germ across the transported
atlas chart inverse.
-/
theorem onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_commonSourceGermEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  have hCommonSource : c.source ∩ t.source ∈ nhds p :=
    (c.open_source.inter t.open_source).mem_nhds ⟨hp, hpt⟩
  have hCommonNhds : ∀ᶠ y in nhds p, c y = t y := by
    rwa [nhdsWithin_eq_nhds.mpr hCommonSource] at hCommon
  have hSymmTendsto :
      Filter.Tendsto c.symm (nhds (c p)) (nhds p) := by
    simpa [c.left_inv hp] using (c.continuousAt_symm (c.map_source hp)).tendsto
  have hPull : ∀ᶠ z in nhds (c p), c (c.symm z) = t (c.symm z) :=
    hSymmTendsto.eventually hCommonNhds
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hPull] with z hzEq hzTarget _hzTransportedSource
  exact hzEq.symm.trans (c.right_inv hzTarget)

/--
The target-preimage right-inverse source is already enough for local identity
of the internal transported-atlas coordinate transition, by restricting from
the transported atlas chart target to the actual transition source.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_targetPreimageRightInv
    (payload :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hRightInv :
      ∀ᶠ z in nhdsWithin (c p) c.target,
        c.symm z ∈ t.source → t (c.symm z) = z := by
    simpa [t] using payload e hc p hp
  have hTransitionSourceSubset : φ.source ⊆ c.target := by
    intro z hzSource
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.1
  have hRightInvOnTransition :
      ∀ᶠ z in nhdsWithin (c p) φ.source,
        c.symm z ∈ t.source → t (c.symm z) = z :=
    hRightInv.filter_mono
      (nhdsWithin_mono _ hTransitionSourceSubset)
  filter_upwards [hRightInvOnTransition, eventually_mem_nhdsWithin] with
      z hzRightInv hzSource
  have hzTransportedSource : c.symm z ∈ t.source := by
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.2
  calc
    φ z = t (c.symm z) := by
      dsimp [φ]
    _ = z := hzRightInv hzTransportedSource

/--
Internal transported-atlas common-source chart-germ equality is equivalent to
local identity of the coordinate transition: pulling the germ forward along the
transported atlas chart gives identity on the actual transition source.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_commonSourceGermEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  have hTransitionAlongChart :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), φ (c y) = c y := by
    filter_upwards [hCommon, eventually_mem_nhdsWithin] with y hEq hySource
    have hTransitionApply : φ (c y) = t y := by
      dsimp [φ]
      rw [c.left_inv hySource.1]
    exact hTransitionApply.trans hEq.symm
  have hOnPreimage :
      ∀ᶠ z in nhdsWithin (c p) (c.symm ⁻¹' (c.source ∩ t.source)),
        φ z = z :=
    (c.eventually_nhdsWithin (fun z => φ z = z) hp).mpr
      hTransitionAlongChart
  have hTransitionSourceSubset :
      φ.source ⊆ c.symm ⁻¹' (c.source ∩ t.source) := by
    intro z hzSource
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact ⟨c.map_target hzSource.1, hzSource.2⟩
  exact hOnPreimage.filter_mono
    (nhdsWithin_mono _ hTransitionSourceSubset)

/--
Internal transported-atlas transition identity pulls back along the transported
atlas chart to give the transported-atlas common-source chart-germ equality.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionId
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u} := by
  intro M _top e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hpTarget : c p ∈ c.target := c.map_source hp
  have hTransition :
      ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z := by
    simpa [t, φ] using payload e hc p hp
  have hTransitionSource :
      φ.source ∈ nhdsWithin (c p) (c.symm ⁻¹' (c.source ∩ t.source)) := by
    rw [mem_nhdsWithin]
    refine ⟨c.target, c.open_target, hpTarget, ?_⟩
    intro z hz
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hz.1, hz.2.2⟩
  have hTransitionOnPreimage :
      ∀ᶠ z in nhdsWithin (c p) (c.symm ⁻¹' (c.source ∩ t.source)),
        φ z = z :=
    hTransition.filter_mono
      (nhdsWithin_le_iff.mpr hTransitionSource)
  have hPull :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), φ (c y) = c y :=
    (c.eventually_nhdsWithin (fun z => φ z = z) hp).mp
      hTransitionOnPreimage
  filter_upwards [hPull, eventually_mem_nhdsWithin] with y hId hySource
  have hTransition_apply : φ (c y) = t y := by
    dsimp [φ]
    rw [c.left_inv hySource.1]
  exact hId.symm.trans hTransition_apply

/--
Conversely, local identity of the internal transported-atlas coordinate
transition supplies the target-preimage right-inverse source through the
common-source chart germ.
-/
theorem onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_transitionId
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} :=
  onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_commonSourceGermEq
    (onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionId
      payload)

/--
Internal transported-atlas transition chart-map agreement supplies the
transported-atlas common-source chart-germ payload.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionChartMapEq
    (payload :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u} :=
  onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionId
    (onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_transitionChartMapEq
      payload)

/--
The internal transported-atlas common-source germ theorem is exactly the same
local chartAt-choice datum as identity of `c.symm ≫ₕ chartAt p` near `c p`.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_iff_transitionId :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u} ↔
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} :=
  ⟨onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_commonSourceGermEq,
    onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionId⟩

/--
The internal transported-atlas transition identity and target-preimage
right-inverse sources are equivalent formulations of the same chartAt-choice
compatibility on the transition source.
-/
theorem onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_iff_targetPreimageRightInv :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} ↔
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} :=
  ⟨onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_transitionId,
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_targetPreimageRightInv⟩

/--
Model-side transition identity source below common-source chart-germ equality:
after passing through the ambient chart, the transition from the ambient chart
to the transported `chartAt` is eventually the identity on its own source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z

/--
Chart-map source below model-side transition identity: on the actual source of
the coordinate transition from the ambient chart to transported `chartAt`, the
transported chart map agrees with the ambient chart map after applying
`c.symm`.  The remaining identity step is then the ambient chart right-inverse.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source,
                t (c.symm z) = c (c.symm z)

/--
Right-inverse source below transition-source chart-map agreement: on the actual
source of the coordinate transition, the transported chart map sends the ambient
inverse-chart point back to the original model point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source,
                t (c.symm z) = z

/--
Target-membership source below transition-source right-inverse behavior: on the
actual source of the coordinate transition, model points eventually lie in the
transported `chartAt` target.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) φ.source,
                z ∈ t.target

/--
Point-target source below transition-source target membership: the represented
ambient-chart point lies in the transported `chartAt` target.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              c p ∈ t.target

/--
Inverse-map source below transition-source right-inverse behavior: after
restricting the actual transition source to the transported target, the ambient
and transported inverse charts agree.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                c.symm z = t.symm z

/--
Selected-target inverse source below inverse-map equality: on the
target-restricted actual transition source, the transported inverse lands back
in the ambient chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                t.symm z ∈ c.source

/--
Selected-target chart equality below inverse-map equality: on the
target-restricted actual transition source, applying the ambient chart after
the transported inverse returns the target model point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                c (t.symm z) = z

/--
Selected-target transported inverse source inclusion: on the target-restricted
actual transition source, known transported inverse source membership is
locally enough to place the inverse point in the ambient chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                t.symm z ∈ t.source → t.symm z ∈ c.source

/--
Selected-target transported inverse chart-map agreement on source: after
applying the transported inverse, chart-map agreement is required only once the
point is known to lie in the ambient chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
                t.symm z ∈ c.source → c (t.symm z) = t (t.symm z)

/--
Model-target transition identity source below the local transition identity:
the transition is compared with the identity only on the common target of the
ambient chart and the transition source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
                c.symm ≫ₕ t
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ φ.source), φ z = z

/--
Model-target chart-map source below transition identity: after moving a model
point back by the ambient inverse chart, the transported `chartAt` map agrees
locally with the ambient chart map on the explicit transition source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
                t (c.symm z) = c (c.symm z)

/--
Right-inverse source below chart-map agreement: the transported `chartAt` map
itself sends the ambient inverse-chart point back to the original model point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
                t (c.symm z) = z

/--
Inverse-map source below target-preimage right-inverse behavior: on the exact
model-side source of the transition, the model point is in the transported
chart target and the two inverse charts agree there.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
                z ∈ t.target ∧ c.symm z = t.symm z

/--
Target-membership source below target-preimage inverse equality: on the explicit
model-side transition source, points eventually lie in the transported
`chartAt` target.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
                z ∈ t.target

/--
Inverse-equality source below target-preimage inverse equality: after restricting
the explicit transition source to the transported target, the ambient and
transported inverse charts agree.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p)
                  ((c.target ∩ c.symm ⁻¹' t.source) ∩ t.target),
                c.symm z = t.symm z

/--
Local target/source equivalence source below transported target membership:
near `c p` in the ambient chart target, membership in the transported chart
target is exactly membership of the ambient inverse point in the transported
chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) c.target,
                (z ∈ t.target ↔ c.symm z ∈ t.source)

/--
Common-target inverse equality source below the target-restricted inverse
equality: on the common target of the ambient chart and transported `chartAt`,
the inverse maps agree locally near `c p`.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                c.symm z = t.symm z

/--
Common-target forward inverse source below common-target inverse equality: on
the common target, the transported inverse point lies in the ambient source and
the ambient chart maps it back to the model point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                t.symm z ∈ c.source ∧ c (t.symm z) = z

/--
Common-target transported inverse source: on the common target, the
transported inverse point lies in the ambient chart source locally near `c p`.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                t.symm z ∈ c.source

/--
Common-target transported inverse chart equality: after applying the
transported inverse, the ambient chart maps back to the model point locally near
`c p`.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                c (t.symm z) = z

/--
Common-target transported inverse source inclusion: on the common target, the
known transported inverse source membership is locally enough to place the
transported inverse point in the ambient chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                t.symm z ∈ t.source → t.symm z ∈ c.source

/--
Common-target transported inverse chart-map agreement: after applying the
transported inverse, the ambient chart agrees with the transported chart locally
near `c p`.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                c (t.symm z) = t (t.symm z)

/--
Target-preimage chart-map agreement on source: on the ambient target, whenever
the ambient inverse point lies in the transported chart source, the transported
and ambient chart maps agree at that point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) c.target,
                c.symm z ∈ t.source → t (c.symm z) = c (c.symm z)

/--
Common-target chart-map agreement on source: after applying the transported
inverse, chart-map agreement is required only once that point is known to lie
in the ambient chart source.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
                t.symm z ∈ c.source → c (t.symm z) = t (t.symm z)

/--
Common-target transported inverse convergence: along the common model target
near `c p`, the transported inverse tends to the manifold point `p`.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                @ChartedSpace.chartAt ThreeManifoldModel _ M _
                  (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                  p
              Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target)) (nhds p)

/--
Pointwise chart equality source below common-target transported inverse
convergence: the ambient chart and transported `chartAt` agree at the source
point.
-/
def OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload :
    Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        ∀ {c : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
            ∀ p ∈ c.source,
              let t : OpenPartialHomeomorph M ThreeManifoldModel :=
                    @ChartedSpace.chartAt ThreeManifoldModel _ M _
                      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
                      p
              c p = t p

/--
Local forward-map agreement near the source point supplies target-preimage
chart-map agreement after pulling back along the ambient inverse chart.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  rcases payload e hc p hp with ⟨u, hu, hpu, hChart⟩
  change Set.EqOn c t (c.source ∩ u) at hChart
  have hSymmTendsto :
      Filter.Tendsto c.symm (nhds (c p)) (nhds p) := by
    simpa [c.left_inv hp] using (c.continuousAt_symm (c.map_source hp)).tendsto
  have hEventuallyU : ∀ᶠ z in nhds (c p), c.symm z ∈ u :=
    hSymmTendsto (hu.mem_nhds hpu)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hEventuallyU] with z hzU hzTarget _hzTransportedSource
  have hzAmbientSource : c.symm z ∈ c.source :=
    c.map_target hzTarget
  exact (hChart ⟨hzAmbientSource, hzU⟩).symm

/--
Local forward-map agreement near the source point supplies pointwise chart
equality at that point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtChartEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  rcases payload e hc p hp with ⟨u, _hu, hpu, hChart⟩
  change Set.EqOn c t (c.source ∩ u) at hChart
  exact hChart ⟨hp, hpu⟩

/--
Full source-germ equality supplies the conditional transported-source
chart-map datum by using only the points where the transported chart is in
source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload_of_localTransportedChartAtSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSource :
      ∀ᶠ y in nhdsWithin p c.source, c y = t y := by
    simpa [t] using payload e hc p hp
  filter_upwards [hSource] with y hy _hyTransportedSource
  exact hy.symm

/--
The conditional source-germ chart-map datum supplies target-preimage chart-map
agreement after pulling back along the ambient inverse chart.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_sourceChartMapEqOnTransportedSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSource :
      ∀ᶠ y in nhdsWithin p c.source,
        y ∈ t.source → t y = c y := by
    simpa [t] using payload e hc p hp
  rw [eventually_nhdsWithin_iff] at hSource
  have hSymmTendsto :
      Filter.Tendsto c.symm (nhds (c p)) (nhds p) := by
    simpa [c.left_inv hp] using (c.continuousAt_symm (c.map_source hp)).tendsto
  have hPull :
      ∀ᶠ z in nhds (c p),
        c.symm z ∈ c.source →
          c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) :=
    hSymmTendsto.eventually hSource
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hPull] with z hzPull hzTarget hzTransportedSource
  exact hzPull (c.map_target hzTarget) hzTransportedSource

/--
The conditional source-germ chart-map datum supplies pointwise chart equality:
the transported chart source is an open neighborhood of the point, so the
conditional eventual equality is an ordinary germ equality at `p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_sourceChartMapEqOnTransportedSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hSource :
      ∀ᶠ y in nhdsWithin p c.source,
        y ∈ t.source → t y = c y := by
    simpa [t] using payload e hc p hp
  rw [eventually_nhdsWithin_iff] at hSource
  have hAmbientSource : ∀ᶠ y in nhds p, y ∈ c.source :=
    c.open_source.mem_nhds hp
  have hTransportedSource : ∀ᶠ y in nhds p, y ∈ t.source :=
    t.open_source.mem_nhds hpt
  have hEq : c =ᶠ[nhds p] t := by
    filter_upwards [hSource, hAmbientSource, hTransportedSource] with y hy hcy hty
    exact (hy hcy hty).symm
  have hcTendsto : Filter.Tendsto c (nhds p) (nhds (c p)) :=
    (c.continuousAt hp).tendsto
  have htTendsto : Filter.Tendsto t (nhds p) (nhds (t p)) :=
    (t.continuousAt hpt).tendsto
  exact tendsto_nhds_unique_of_eventuallyEq hcTendsto htTendsto hEq

/--
Chart-map agreement on the explicit target-preimage source supplies transported
target membership using the transported chart source law and ambient chart
right-inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetPreimageChartMapEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hChartMapEq :
      ∀ᶠ z in nhdsWithin (c p) c.target,
        c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) := by
    simpa [t] using payload e hc p hp
  have hChartMapEqOnSource :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        c.symm z ∈ t.source → t (c.symm z) = c (c.symm z) :=
    hChartMapEq.filter_mono (nhdsWithin_mono _ Set.inter_subset_left)
  filter_upwards [hChartMapEqOnSource, eventually_mem_nhdsWithin] with z hzEq hzSource
  have hzImageTarget : t (c.symm z) ∈ t.target :=
    t.map_source hzSource.2
  have hzEqTarget : t (c.symm z) = z :=
    (hzEq hzSource.2).trans (c.right_inv hzSource.1)
  simpa [hzEqTarget] using hzImageTarget

/--
The common-target source-inclusion fact plus conditional chart-map agreement
supplies unconditional common-target chart-map agreement.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload_of_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
    (commonTargetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u})
    (commonTargetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSourceIncl :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ t.source → t.symm z ∈ c.source := by
    simpa [t] using commonTargetSymmSourceInclusion e hc p hp
  have hChartMapEqOnSource :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source → c (t.symm z) = t (t.symm z) := by
    simpa [t] using commonTargetSymmChartMapEqOnSource e hc p hp
  filter_upwards [hSourceIncl, hChartMapEqOnSource, eventually_mem_nhdsWithin]
    with z hzSourceIncl hzChartMapEq hzCommon
  exact hzChartMapEq (hzSourceIncl (t.map_target hzCommon.2))

/--
Common-target transported inverse convergence supplies the source-inclusion
payload by applying it to the open ambient chart source neighborhood of `p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_commonTargetSymmTendsto
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hTendsto :
      Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target)) (nhds p) := by
    simpa [t] using payload e hc p hp
  have hSource : ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
      t.symm z ∈ c.source :=
    hTendsto (c.open_source.mem_nhds hp)
  filter_upwards [hSource] with z hzSource _hzTransportedSource
  exact hzSource

/--
The target-preimage chart-map payload plus common-target transported inverse
convergence supplies conditional chart-map agreement after applying the
transported inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (commonTargetSymmTendsto :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hTargetPreimage :
      ∀ᶠ w in nhdsWithin (c p) c.target,
        c.symm w ∈ t.source → t (c.symm w) = c (c.symm w) := by
    simpa [t] using targetPreimageChartMapEqOnSource e hc p hp
  rw [eventually_nhdsWithin_iff] at hTargetPreimage
  have hTendsto :
      Filter.Tendsto t.symm (nhdsWithin (c p) (c.target ∩ t.target)) (nhds p) := by
    simpa [t] using commonTargetSymmTendsto e hc p hp
  have hChartTendsto :
      Filter.Tendsto (fun z => c (t.symm z))
        (nhdsWithin (c p) (c.target ∩ t.target)) (nhds (c p)) :=
    by
      simpa [Function.comp_def] using (c.continuousAt hp).tendsto.comp hTendsto
  have hPull :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) ∈ c.target →
          c.symm (c (t.symm z)) ∈ t.source →
            t (c.symm (c (t.symm z))) = c (c.symm (c (t.symm z))) :=
    hChartTendsto.eventually hTargetPreimage
  filter_upwards [hPull, eventually_mem_nhdsWithin] with z hzPull hzCommon hzAmbientSource
  have hLeft : c.symm (c (t.symm z)) = t.symm z :=
    c.left_inv hzAmbientSource
  have hzChartTarget : c (t.symm z) ∈ c.target :=
    c.map_source hzAmbientSource
  have hzTransportedSource : c.symm (c (t.symm z)) ∈ t.source := by
    rw [hLeft]
    exact t.map_target hzCommon.2
  have hEq := hzPull hzChartTarget hzTransportedSource
  simpa [hLeft] using hEq.symm

/--
Pointwise chart equality supplies common-target transported inverse
convergence using continuity of the transported inverse chart.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hPoint : c p = t p := by
    simpa [t] using payload e hc p hp
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hcpTarget : c p ∈ t.target := by
    rw [hPoint]
    exact t.map_source hpt
  have hSymm : t.symm (c p) = p := by
    rw [hPoint]
    exact t.left_inv hpt
  have hTendstoFull :
      Filter.Tendsto t.symm (nhds (c p)) (nhds p) := by
    simpa [hSymm] using (t.continuousAt_symm hcpTarget).tendsto
  exact hTendstoFull.mono_left nhdsWithin_le_nhds

/--
Pointwise chart equality closes the common-target source-inclusion field by
first producing convergence of the transported inverse back to the source point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_pointChartEq
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_commonTargetSymmTendsto
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
      pointChartEq)

/--
Target-preimage chart-map agreement plus pointwise chart equality close the
conditional common-target chart-map field through transported inverse
convergence.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
    targetPreimageChartMapEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
      pointChartEq)

/--
Common-source chart-germ equality supplies target-preimage chart-map agreement
after pulling the germ across the ambient inverse chart.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_commonSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  have hCommonSource : c.source ∩ t.source ∈ nhds p :=
    (c.open_source.inter t.open_source).mem_nhds ⟨hp, hpt⟩
  have hCommonNhds : ∀ᶠ y in nhds p, c y = t y := by
    rwa [nhdsWithin_eq_nhds.mpr hCommonSource] at hCommon
  have hSymmTendsto :
      Filter.Tendsto c.symm (nhds (c p)) (nhds p) := by
    simpa [c.left_inv hp] using (c.continuousAt_symm (c.map_source hp)).tendsto
  have hPull : ∀ᶠ z in nhds (c p), c (c.symm z) = t (c.symm z) :=
    hSymmTendsto.eventually hCommonNhds
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hPull] with z hzEq _hzTarget _hzTransportedSource
  exact hzEq.symm

/--
Common-source chart-germ equality supplies pointwise chart equality by
continuity and uniqueness of limits at the source point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_commonSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  have hCommonSource : c.source ∩ t.source ∈ nhds p :=
    (c.open_source.inter t.open_source).mem_nhds ⟨hp, hpt⟩
  have hCommonNhds : c =ᶠ[nhds p] t := by
    rwa [nhdsWithin_eq_nhds.mpr hCommonSource] at hCommon
  have hcTendsto : Filter.Tendsto c (nhds p) (nhds (c p)) :=
    (c.continuousAt hp).tendsto
  have htTendsto : Filter.Tendsto t (nhds p) (nhds (t p)) :=
    (t.continuousAt hpt).tendsto
  exact tendsto_nhds_unique_of_eventuallyEq hcTendsto htTendsto hCommonNhds

/--
Common-source chart-germ equality supplies the conditional source-chart-map
datum directly: the transported `chartAt` source is already a neighborhood of
the source point, so the common-source germ can be read on `𝓝[c.source] p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload_of_commonSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have htSource : t.source ∈ nhds p :=
    t.open_source.mem_nhds hpt
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  have hSource : ∀ᶠ y in nhdsWithin p c.source, c y = t y := by
    change ∀ᶠ y in nhdsWithin p c.source, c y = t y
    rwa [nhdsWithin_restrict' c.source htSource]
  filter_upwards [hSource] with y hy _hyTransportedSource
  exact hy.symm

/--
The local source-inclusion fact supplies the common-target transported inverse
ambient-source membership, using the transported chart target inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload_of_commonTargetSymmSourceInclusion
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hIncl :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ t.source → t.symm z ∈ c.source := by
    simpa [t] using payload e hc p hp
  filter_upwards [hIncl, eventually_mem_nhdsWithin] with z hzIncl hzCommon
  exact hzIncl (t.map_target hzCommon.2)

/--
The local chart-map agreement after transported inverse supplies the
common-target transported inverse chart equality, using the transported chart
right-inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload_of_commonTargetSymmChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hChartMapEq :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) = t (t.symm z) := by
    simpa [t] using payload e hc p hp
  filter_upwards [hChartMapEq, eventually_mem_nhdsWithin] with z hzEq hzCommon
  calc
    c (t.symm z) = t (t.symm z) := hzEq
    _ = z := t.right_inv hzCommon.2

/--
The split common-target source and chart-equality facts supply the accepted
common-target forward inverse source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
    (commonTargetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u})
    (commonTargetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hSource :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source := by
    simpa [t] using commonTargetSymmSource e hc p hp
  have hChartEq :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) = z := by
    simpa [t] using commonTargetSymmChartEq e hc p hp
  filter_upwards [hSource, hChartEq] with z hzSource hzChartEq
  exact ⟨hzSource, hzChartEq⟩

/--
The one-sided target membership fact plus common-target inverse equality
supplies the local target/source equivalence.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload_of_targetPreimageTargetMem_and_commonTargetInvEq
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (commonTargetInvEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hTargetMem :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        z ∈ t.target := by
    simpa [t] using targetMem e hc p hp
  have hCommonInv :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c.symm z = t.symm z := by
    simpa [t] using commonTargetInvEq e hc p hp
  rw [eventually_nhdsWithin_iff] at hTargetMem hCommonInv ⊢
  filter_upwards [hTargetMem, hCommonInv] with z hMem hInv hzTarget
  constructor
  · intro hzTransportedTarget
    have hEq : c.symm z = t.symm z := hInv ⟨hzTarget, hzTransportedTarget⟩
    rw [hEq]
    exact t.map_target hzTransportedTarget
  · intro hzTransportedSource
    exact hMem ⟨hzTarget, hzTransportedSource⟩

/--
The common-target forward inverse source supplies common-target inverse equality
by applying the ambient chart left-inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload_of_commonTargetSymmSourceChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hForward :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source ∧ c (t.symm z) = z := by
    simpa [t] using payload e hc p hp
  filter_upwards [hForward] with z hz
  calc
    c.symm z = c.symm (c (t.symm z)) := by rw [hz.2]
    _ = t.symm z := c.left_inv hz.1

/--
Local target/source equivalence supplies transported target membership on the
explicit transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetSourceIff
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hIff : ∀ᶠ z in nhdsWithin (c p) c.target,
      (z ∈ t.target ↔ c.symm z ∈ t.source) := by
    simpa [t] using payload e hc p hp
  have hIffOnSource :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        (z ∈ t.target ↔ c.symm z ∈ t.source) :=
    hIff.filter_mono (nhdsWithin_mono _ Set.inter_subset_left)
  filter_upwards [hIffOnSource, eventually_mem_nhdsWithin] with z hzIff hzSource
  exact hzIff.mpr hzSource.2

/--
Common-target inverse equality supplies inverse equality after the explicit
transition source has been restricted to the transported target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload_of_commonTargetInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hInv : ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
      c.symm z = t.symm z := by
    simpa [t] using payload e hc p hp
  exact hInv.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩)

/--
Target membership on the explicit transition source plus inverse equality on
the transported-target restriction supplies the accepted target/inverse payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload_of_targetPreimageTargetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let A : Set ThreeManifoldModel := c.target ∩ c.symm ⁻¹' t.source
  have hTarget : ∀ᶠ z in nhdsWithin (c p) A, z ∈ t.target := by
    simpa [t, A] using targetMem e hc p hp
  have hInvOnTarget :
      ∀ᶠ z in nhdsWithin (c p) (A ∩ t.target), c.symm z = t.symm z := by
    simpa [t, A] using invEqOnTarget e hc p hp
  have hTargetSet : t.target ∈ nhdsWithin (c p) A := hTarget
  have hInv : ∀ᶠ z in nhdsWithin (c p) A, c.symm z = t.symm z := by
    rwa [nhdsWithin_inter_of_mem' hTargetSet] at hInvOnTarget
  filter_upwards [hTarget, hInv] with z hzTarget hzInv
  exact ⟨hzTarget, hzInv⟩

/--
The target/inverse source supplies the target-preimage right-inverse behavior by
rewriting `c.symm z` to `t.symm z` and using the transported chart right-inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload_of_localTransportedChartAtTargetPreimageTargetInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hTargetInv :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        z ∈ t.target ∧ c.symm z = t.symm z := by
    simpa [t] using payload e hc p hp
  filter_upwards [hTargetInv] with z hz
  calc
    t (c.symm z) = t (t.symm z) := by
      rw [hz.2]
    _ = z := t.right_inv hz.1

/--
The right-inverse source supplies chart-map agreement by applying the ambient
chart right-inverse law on `c.target`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload_of_localTransportedChartAtTargetPreimageRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hRightInv :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        t (c.symm z) = z := by
    simpa [t] using payload e hc p hp
  filter_upwards [hRightInv, eventually_mem_nhdsWithin] with z hEq hzSource
  calc
    t (c.symm z) = z := hEq
    _ = c (c.symm z) := (c.right_inv hzSource.1).symm

/--
The explicit target-preimage right-inverse source supplies right-inverse behavior
on the actual source of the ambient-to-transported transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_localTransportedChartAtTargetPreimageRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        t (c.symm z) = z := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz)

/--
Target membership on the actual transition source and inverse-map equality on
the target-restricted transition source supply transported right-inverse
behavior.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hTargetMem :
      ∀ᶠ z in nhdsWithin (c p) φ.source, z ∈ t.target := by
    simpa [t, φ] using targetMem e hc p hp
  have hInvEq :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        c.symm z = t.symm z := by
    simpa [t, φ] using invEqOnTarget e hc p hp
  have hRestrict : φ.source ∩ t.target ∈ nhdsWithin (c p) φ.source := by
    filter_upwards [eventually_mem_nhdsWithin, hTargetMem] with z hzSource hzTarget
    exact ⟨hzSource, hzTarget⟩
  have hInvEqOnSource :
      ∀ᶠ z in nhdsWithin (c p) φ.source, c.symm z = t.symm z :=
    hInvEq.filter_mono (nhdsWithin_le_iff.mpr hRestrict)
  filter_upwards [hTargetMem, hInvEqOnSource] with z hzTarget hzInvEq
  calc
    t (c.symm z) = t (t.symm z) := by rw [hzInvEq]
    _ = z := t.right_inv hzTarget

/--
Point target membership supplies transported target membership on the actual
transition source by openness of the transported chart target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPointTarget : c p ∈ t.target := by
    simpa [t] using payload e hc p hp
  have hTarget : ∀ᶠ z in nhds (c p), z ∈ t.target :=
    t.open_target.mem_nhds hPointTarget
  exact hTarget.filter_mono nhdsWithin_le_nhds

/--
Pointwise chart equality supplies point target membership for transported
`chartAt`, using the transported chart source law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have hPointEq : c p = t p := by
    simpa [t] using payload e hc p hp
  simpa [hPointEq] using t.map_source hpt

/--
The explicit target-preimage target-membership source supplies target membership
on the actual source of the ambient-to-transported transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_localTransportedChartAtTargetPreimageTargetMem
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        z ∈ t.target := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz)

/--
The explicit target-preimage inverse-equality source supplies inverse-map
equality on the transported-target restriction of the actual transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_localTransportedChartAtTargetPreimageInvEqOnTarget
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p)
          ((c.target ∩ c.symm ⁻¹' t.source) ∩ t.target),
        c.symm z = t.symm z := by
    simpa [t] using payload e hc p hp
  simpa [φ, OpenPartialHomeomorph.trans_source] using hPayload

/--
The broader common-target source-membership fact supplies the selected-target
source-membership fact by restricting to the actual transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonTargetSymmSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
The broader common-target chart-equality fact supplies the selected-target
chart-equality fact by restricting to the actual transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonTargetSymmChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) = z := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
The broader common-target source-inclusion fact supplies the selected-target
source-inclusion fact by restricting to the actual transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_commonTargetSymmSourceInclusion
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ t.source → t.symm z ∈ c.source := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
The broader common-target conditional chart-map fact supplies the
selected-target conditional chart-map fact by restricting to the actual
transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_commonTargetSymmChartMapEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source → c (t.symm z) = t (t.symm z) := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      have hz' : z ∈ (c.target ∩ c.symm ⁻¹' t.source) ∩ t.target := by
        simpa [t, φ, OpenPartialHomeomorph.trans_source] using hz
      exact ⟨hz'.1.1, hz'.2⟩)

/--
Pointwise chart equality supplies selected-target source inclusion by first
giving common-target transported inverse convergence.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_pointChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_commonTargetSymmSourceInclusion
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_pointChartEq
      payload)

/--
Target-preimage chart-map agreement plus pointwise chart equality supplies
selected-target conditional chart-map agreement after the transported inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_commonTargetSymmChartMapEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
      targetPreimageChartMapEqOnSource pointChartEq)

/--
The selected-target source-inclusion fact supplies selected-target transported
inverse source membership, using the transported chart target inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonSourceTransitionTargetSymmSourceInclusion
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hIncl :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ t.source → t.symm z ∈ c.source := by
    simpa [t, φ] using payload e hc p hp
  filter_upwards [hIncl, eventually_mem_nhdsWithin] with z hzIncl hzCommon
  exact hzIncl (t.map_target hzCommon.2)

/--
The selected-target source-inclusion fact plus conditional chart-map agreement
supplies selected-target chart equality by applying transported chart
`right_inv`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource
    (targetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u})
    (targetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hSourceIncl :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ t.source → t.symm z ∈ c.source := by
    simpa [t, φ] using targetSymmSourceInclusion e hc p hp
  have hChartMapEqOnSource :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ c.source → c (t.symm z) = t (t.symm z) := by
    simpa [t, φ] using targetSymmChartMapEqOnSource e hc p hp
  filter_upwards [hSourceIncl, hChartMapEqOnSource, eventually_mem_nhdsWithin]
    with z hzSourceIncl hzChartMapEq hzCommon
  calc
    c (t.symm z) = t (t.symm z) := hzChartMapEq (hzSourceIncl (t.map_target hzCommon.2))
    _ = z := t.right_inv hzCommon.2

/--
Selected-target transported inverse source membership and chart equality supply
inverse-map equality on the target-restricted transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
    (targetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u})
    (targetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hSource :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        t.symm z ∈ c.source := by
    simpa [t, φ] using targetSymmSource e hc p hp
  have hChartEq :
      ∀ᶠ z in nhdsWithin (c p) (φ.source ∩ t.target),
        c (t.symm z) = z := by
    simpa [t, φ] using targetSymmChartEq e hc p hp
  filter_upwards [hSource, hChartEq] with z hzSource hzChartEq
  calc
    c.symm z = c.symm (c (t.symm z)) := by rw [hzChartEq]
    _ = t.symm z := c.left_inv hzSource

/--
Common-target transported inverse source membership and chart equality supply
inverse-map equality on the target-restricted transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
    (commonTargetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u})
    (commonTargetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hSource :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        t.symm z ∈ c.source := by
    simpa [t] using commonTargetSymmSource e hc p hp
  have hChartEq :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ t.target),
        c (t.symm z) = z := by
    simpa [t] using commonTargetSymmChartEq e hc p hp
  have hRestrict :
      nhdsWithin (c p) (φ.source ∩ t.target) ≤
        nhdsWithin (c p) (c.target ∩ t.target) :=
    nhdsWithin_mono _ <| by
      intro z hz
      have hzTransition : z ∈ φ.source := hz.1
      rw [OpenPartialHomeomorph.trans_source] at hzTransition
      exact ⟨hzTransition.1, hz.2⟩
  filter_upwards [hSource.filter_mono hRestrict, hChartEq.filter_mono hRestrict]
    with z hzSource hzChartEq
  calc
    c.symm z = c.symm (c (t.symm z)) := by rw [hzChartEq]
    _ = t.symm z := c.left_inv hzSource

/--
Right-inverse behavior on the actual transition source supplies chart-map
agreement there by applying the ambient chart right-inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hRightInv :
      ∀ᶠ z in nhdsWithin (c p) φ.source,
        t (c.symm z) = z := by
    simpa [t, φ] using payload e hc p hp
  filter_upwards [hRightInv, eventually_mem_nhdsWithin] with z hEq hzSource
  have hzTarget : z ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.1
  calc
    t (c.symm z) = z := hEq
    _ = c (c.symm z) := (c.right_inv hzTarget).symm

/--
The explicit target-preimage chart-map source supplies chart-map agreement on
the actual source of the ambient-to-transported transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtTargetPreimageChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hPayload :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
        t (c.symm z) = c (c.symm z) := by
    simpa [t] using payload e hc p hp
  exact hPayload.filter_mono
    (nhdsWithin_mono _ <| by
      intro z hz
      simpa [φ, OpenPartialHomeomorph.trans_source] using hz)

/--
Chart-map agreement on the actual transition source supplies model-side
transition identity by unfolding the transition and applying the ambient chart
right-inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hMapEq :
      ∀ᶠ z in nhdsWithin (c p) φ.source,
        t (c.symm z) = c (c.symm z) := by
    simpa [t, φ] using payload e hc p hp
  filter_upwards [hMapEq, eventually_mem_nhdsWithin] with z hEq hzSource
  have hzTarget : z ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hzSource
    exact hzSource.1
  calc
    φ z = t (c.symm z) := by
      dsimp [φ]
    _ = c (c.symm z) := hEq
    _ = z := c.right_inv hzTarget

/--
The explicit chart-map source supplies the accepted model-target transition
identity by unfolding the transition and applying the ambient chart inverse law.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload_of_localTransportedChartAtTargetPreimageChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hMapEq :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ φ.source),
        t (c.symm z) = c (c.symm z) := by
    have hPayload :
        ∀ᶠ z in nhdsWithin (c p) (c.target ∩ c.symm ⁻¹' t.source),
          t (c.symm z) = c (c.symm z) := by
      simpa [t] using payload e hc p hp
    exact hPayload.filter_mono
      (nhdsWithin_mono _ <| by
        intro z hz
        simpa [φ, OpenPartialHomeomorph.trans_source] using hz)
  filter_upwards [hMapEq, eventually_mem_nhdsWithin] with z hEq hzSource
  have hzTarget : z ∈ c.target := hzSource.1
  calc
    φ z = t (c.symm z) := by
      dsimp [φ]
    _ = c (c.symm z) := hEq
    _ = z := c.right_inv hzTarget

/--
The model-target transition identity supplies the accepted transition identity,
since the ambient chart target is an open neighborhood of `c p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonTargetTransitionId
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hpTarget : c p ∈ c.target := c.map_source hp
  have hTarget : c.target ∈ nhds (c p) :=
    c.open_target.mem_nhds hpTarget
  have hCommonTarget :
      ∀ᶠ z in nhdsWithin (c p) (c.target ∩ φ.source), φ z = z := by
    simpa [t, φ] using payload e hc p hp
  change ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z
  rw [nhdsWithin_restrict' φ.source hTarget]
  rw [Set.inter_comm]
  exact hCommonTarget

/--
The model-side transition identity pulls back along the ambient chart to give
the common-source chart-germ equality on the manifold side.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  let φ : OpenPartialHomeomorph ThreeManifoldModel ThreeManifoldModel :=
    c.symm ≫ₕ t
  have hpTarget : c p ∈ c.target := c.map_source hp
  have hTransition :
      ∀ᶠ z in nhdsWithin (c p) φ.source, φ z = z := by
    simpa [t, φ] using payload e hc p hp
  have hTransitionSource :
      φ.source ∈ nhdsWithin (c p) (c.symm ⁻¹' (c.source ∩ t.source)) := by
    rw [mem_nhdsWithin]
    refine ⟨c.target, c.open_target, hpTarget, ?_⟩
    intro z hz
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hz.1, hz.2.2⟩
  have hTransitionOnPreimage :
      ∀ᶠ z in nhdsWithin (c p) (c.symm ⁻¹' (c.source ∩ t.source)),
        φ z = z :=
    hTransition.filter_mono
      (nhdsWithin_le_iff.mpr hTransitionSource)
  have hPull :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), φ (c y) = c y :=
    (c.eventually_nhdsWithin (fun z => φ z = z) hp).mp
      hTransitionOnPreimage
  filter_upwards [hPull, eventually_mem_nhdsWithin] with y hId hySource
  have hTransition_apply : φ (c y) = t y := by
    dsimp [φ]
    rw [c.left_inv hySource.1]
  exact hId.symm.trans hTransition_apply

/--
Common-source chart-germ equality supplies the accepted source-germ equality,
since the transported `chartAt` source is itself a neighborhood of the point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hpt : p ∈ t.source := by
    change
      p ∈
        (@ChartedSpace.chartAt ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
    exact @mem_chart_source ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
  have htSource : t.source ∈ nhds p :=
    t.open_source.mem_nhds hpt
  have hCommon :
      ∀ᶠ y in nhdsWithin p (c.source ∩ t.source), c y = t y := by
    simpa [t] using payload e hc p hp
  change ∀ᶠ y in nhdsWithin p c.source, c y = t y
  rwa [nhdsWithin_restrict' c.source htSource]

/--
Common-source transition identity supplies the source-restricted chart germ
through the common-source chart-germ payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)

/--
The source-restricted filter germ supplies the open-neighborhood pointwise
agreement payload by extracting an open neighborhood from `𝓝[c.source] p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hGerm : ∀ᶠ y in nhdsWithin p c.source, c y = t y := by
    simpa [t] using payload e hc p hp
  rw [eventually_nhdsWithin_iff] at hGerm
  rcases eventually_nhds_iff.mp hGerm with ⟨u, hAgree, hu, hpu⟩
  refine ⟨u, hu, hpu, ?_⟩
  change Set.EqOn c t (c.source ∩ u)
  intro y hy
  exact hAgree y hy.2 hy.1

/--
The source-restricted filter germ supplies target-preimage chart-map agreement
through the local open-neighborhood chart equality payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      payload)

/--
The source-restricted filter germ supplies pointwise chart equality through the
local open-neighborhood chart equality payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtChartEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      payload)

/--
Common-source transition identity supplies target-preimage chart-map agreement
through the source-restricted chart germ.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionId
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)

/--
Common-source transition identity supplies pointwise chart equality through the
source-restricted chart germ.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionId
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)

/--
Transition-source chart-map agreement supplies the source-restricted chart germ
through common-source transition identity.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)

/--
Transition-source chart-map agreement supplies target-preimage chart-map
agreement through common-source transition identity.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)

/--
Transition-source chart-map agreement supplies pointwise chart equality through
common-source transition identity.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)

/--
Transition-source right-inverse behavior supplies the source-restricted chart
germ through transition-source chart-map agreement.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)

/--
Transition-source right-inverse behavior supplies target-preimage chart-map
agreement through transition-source chart-map agreement.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)

/--
Transition-source right-inverse behavior supplies pointwise chart equality
through transition-source chart-map agreement.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtSourceGermEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)

/--
The split target-membership and inverse-equality facts supply transition-source
chart-map agreement through the right-inverse payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
The split target-membership and inverse-equality facts supply target-preimage
chart-map agreement through the right-inverse payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
The split target-membership and inverse-equality facts supply pointwise chart
equality through the right-inverse payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
Local forward-map agreement supplies restricted-chart source-equivalence after
shrinking to the common source of the ambient chart and transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  rcases payload e hc p hp with ⟨u, hu, hpu, hChart⟩
  change Set.EqOn c t (c.source ∩ u) at hChart
  let v : Set M := (c.source ∩ t.source) ∩ u
  have hv : IsOpen v := (c.open_source.inter t.open_source).inter hu
  have hpv : p ∈ v := by
    have hpt : p ∈ t.source := by
      change
        p ∈
          (@ChartedSpace.chartAt ThreeManifoldModel _ M _
            (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p).source
      exact @mem_chart_source ThreeManifoldModel M _ _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) p
    exact ⟨⟨hp, hpt⟩, hpu⟩
  refine ⟨v, hv, hpv, ?_⟩
  constructor
  · rw [OpenPartialHomeomorph.restr_source' _ v hv,
      OpenPartialHomeomorph.restr_source' _ v hv]
    ext y
    constructor
    · intro hy
      dsimp [v] at hy ⊢
      exact ⟨hy.2.1.2, hy.2⟩
    · intro hy
      dsimp [v] at hy ⊢
      exact ⟨hy.2.1.1, hy.2⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restr_source' _ v hv] at hy
    have hyChartSource : y ∈ c.source ∩ u := by
      exact ⟨hy.1, hy.2.2⟩
    simpa using hChart hyChartSource

/--
The source-restricted filter germ supplies restricted-chart source-equivalence
through the open-neighborhood chart-agreement payload.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      payload)

/--
Local equality of restricted charts supplies the weaker restricted-chart
source-equivalence germ.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtRestrEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc p hp
  rcases payload e hc p hp with ⟨u, hu, hpu, hRestr⟩
  refine ⟨u, hu, hpu, ?_⟩
  rw [hRestr]

/--
The restricted-chart source-equivalence germ gives exactly the local source
intersection equality and forward-map agreement used by the accepted
manifold-side chart-germ route.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  let p : M := c.symm x
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hp : p ∈ c.source := c.map_target hx
  rcases payload e hc p hp with ⟨u, hu, hpu, hEqOnSource⟩
  change c.restr u ≈ t.restr u at hEqOnSource
  refine ⟨u, hu, hpu, ?_, ?_⟩
  · have hSource : (c.restr u).source = (t.restr u).source :=
      hEqOnSource.1
    rw [OpenPartialHomeomorph.restr_source' _ u hu,
      OpenPartialHomeomorph.restr_source' _ u hu] at hSource
    exact hSource
  · intro y hy
    have hySource : y ∈ (c.restr u).source := by
      rw [OpenPartialHomeomorph.restr_source' _ u hu]
      exact hy
    exact hEqOnSource.2 hySource

/--
Local equality of restricted forward charts supplies the source-intersection and
forward-map equality germ.  This is the charted-space germ form of the remaining
`chartAt` comparison, expressed at the actual manifold source point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  let p : M := c.symm x
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      p
  have hp : p ∈ c.source := c.map_target hx
  rcases payload e hc p hp with ⟨u, hu, hpu, hRestr⟩
  change c.restr u = t.restr u at hRestr
  refine ⟨u, hu, hpu, ?_, ?_⟩
  · have hSource :
        (c.restr u).source = (t.restr u).source :=
      congrArg (fun e : OpenPartialHomeomorph M ThreeManifoldModel => e.source)
        hRestr
    rw [OpenPartialHomeomorph.restr_source' _ u hu,
      OpenPartialHomeomorph.restr_source' _ u hu] at hSource
    exact hSource
  · intro y hy
    have hFun :
        ((c.restr u : OpenPartialHomeomorph M ThreeManifoldModel) :
            M → ThreeManifoldModel) =
          ((t.restr u : OpenPartialHomeomorph M ThreeManifoldModel) :
            M → ThreeManifoldModel) :=
      congrArg (fun e : OpenPartialHomeomorph M ThreeManifoldModel =>
        (e : M → ThreeManifoldModel)) hRestr
    exact congrFun hFun y

/--
The local source-intersection and forward-chart equality germ gives the
model-side local target equality and inverse-map equality.  The target
neighborhood is the ambient chart image of the manifold-side neighborhood.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      (c.symm x)
  rcases payload e hc x hx with ⟨u, hu, hxu, hSource, hChart⟩
  change c.source ∩ u = t.source ∩ u at hSource
  change Set.EqOn c t (c.source ∩ u) at hChart
  refine ⟨c '' (c.source ∩ u), c.isOpen_image_source_inter hu, ?_, ?_, ?_⟩
  · exact ⟨c.symm x, ⟨c.map_target hx, hxu⟩, c.right_inv hx⟩
  · apply Set.Subset.antisymm
    · intro y hy
      rcases hy.2 with ⟨z, hz, hzy⟩
      have hzt : z ∈ t.source ∩ u := by
        simpa [hSource] using hz
      have hChart_z : c z = t z := hChart hz
      have hyTarget : y ∈ t.target := by
        rw [← hzy, hChart_z]
        exact t.map_source hzt.1
      exact ⟨hyTarget, hy.2⟩
    · intro y hy
      rcases hy.2 with ⟨z, hz, hzy⟩
      have hyTarget : y ∈ c.target := by
        rw [← hzy]
        exact c.map_source hz.1
      exact ⟨hyTarget, hy.2⟩
  · intro y hy
    rcases hy.2 with ⟨z, hz, hzy⟩
    have hzt : z ∈ t.source ∩ u := by
      simpa [hSource] using hz
    have hChart_z : c z = t z := hChart hz
    have hcSymm : c.symm y = z := by
      rw [← hzy]
      exact c.left_inv hz.1
    have htSymm : t.symm y = z := by
      rw [← hzy, hChart_z]
      exact t.left_inv hzt.1
    rw [hcSymm, htSymm]

/--
The restricted-chart source-equivalence germ supplies the model-side local target
equality and inverse-map equality through the accepted manifold-side chart-germ
route.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtRestrEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEqOnSource
      payload)

/--
The local forward-map agreement chart-germ source supplies the model-side local
target equality and inverse-map equality through the restricted-chart
source-equivalence route.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtChartEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtRestrEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
      payload)

/--
The local restriction-equality chart-germ source supplies the model-side local
target equality and inverse-map equality through the accepted manifold-side
chart-germ route.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtRestrEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEq
      payload)

/--
The unfolded local target/source and inverse-map identities supply the
accepted restricted inverse-chart source-equivalence payload.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  rcases payload e hc x hx with ⟨s, hs, hxs, hTarget, hInv⟩
  refine ⟨s, hs, hxs, ?_⟩
  constructor
  · rw [OpenPartialHomeomorph.restr_source' _ s hs,
      OpenPartialHomeomorph.restr_source' _ s hs]
    simpa [OpenPartialHomeomorph.symm_source] using hTarget
  · intro y hy
    rw [OpenPartialHomeomorph.restr_source' _ s hs] at hy
    have hyTarget : y ∈ c.target ∩ s := by
      simpa [OpenPartialHomeomorph.symm_source] using hy
    simpa using hInv hyTarget

/--
The manifold-side local source-intersection and forward-chart equality germ
supplies the accepted source-equivalence inverse-chart payload.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtSourceEqChartEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
      payload)

/--
The restricted-chart source-equivalence germ supplies the accepted
source-equivalence inverse-chart payload.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtRestrEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtSourceEqChartEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEqOnSource
      payload)

/--
The local forward-map agreement chart-germ source supplies the accepted
source-equivalence inverse-chart payload.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtRestrEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
      payload)

/--
The local restriction-equality chart-germ source supplies the accepted
source-equivalence inverse-chart payload.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtRestrEq
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} :=
  onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localTransportedChartAtSourceEqChartEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEq
      payload)

/--
Bundled equality of the restricted inverse charts supplies the weaker
source-equivalence datum.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  rcases payload e hc x hx with ⟨s, hs, hxs, hEq⟩
  refine ⟨s, hs, hxs, ?_⟩
  rw [hEq]

/--
The canonical transported `chartAt` local inverse model supplies the accepted
inverse-atlas normal form, using the built-in chart-atlas membership theorem
for the transported charted-space instance.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc x hx
  rcases payload e hc x hx with ⟨s, hs, hxs, hEq⟩
  refine ⟨s, hs, hxs,
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      (c.symm x), ?_, hEq⟩
  exact @chart_mem_atlas ThreeManifoldModel M _ _
    (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
    (c.symm x)

/--
The inverse-chart normal form supplies the accepted local transition model by
composing the locally equal inverse-chart restrictions with the transported
target chart.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedAtlasModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd x hx
  have hxTarget : x ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  rcases payload e hc x hxTarget with ⟨s, hs, hxs, t, ht, hEq⟩
  refine ⟨s, hs, hxs, t, ht, ?_⟩
  rw [← OpenPartialHomeomorph.restr_trans, hEq,
    OpenPartialHomeomorph.restr_trans]

/--
The canonical transported `chartAt` inverse model supplies the local
transition normal-form source through the accepted inverse-atlas model.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u} :=
  onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedAtlasModel
    (onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      payload)

/--
The weaker source-equivalence normal form is enough for the local restricted
transition theorem, because transported-atlas transition membership can be
transported across `EqOnSource`.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd x hx
  have hxTarget : x ∈ c.target := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  rcases payload e hc x hxTarget with ⟨s, hs, hxs, hEqOn⟩
  refine ⟨s, hs, hxs, ?_⟩
  let t : OpenPartialHomeomorph M ThreeManifoldModel :=
    @ChartedSpace.chartAt ThreeManifoldModel _ M _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      (c.symm x)
  have ht :
      t ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    @chart_mem_atlas ThreeManifoldModel M _ _
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e)
      (c.symm x)
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  have hSmooth : IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedSmoothabilityBridgePayload e
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := hSmooth
  have hTransported :
      t.symm ≫ₕ d ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
    HasGroupoid.compatible ht hd
  have hRestr :
      (t.symm ≫ₕ d).restr s ∈
        contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
    closedUnderRestriction' hTransported hs
  have hEqOnTransition :
      (c.symm ≫ₕ d).restr s ≈ (t.symm ≫ₕ d).restr s := by
    rw [← OpenPartialHomeomorph.restr_trans,
      ← OpenPartialHomeomorph.restr_trans]
    exact OpenPartialHomeomorph.EqOnSource.trans' hEqOn
      (OpenPartialHomeomorph.eqOnSource_refl d)
  exact StructureGroupoid.mem_of_eqOnSource
    (contDiffGroupoid 1 ThreeManifoldModelWithCorners)
    hRestr hEqOnTransition

/--
The unfolded local target/source and inverse-map identities close the local
restricted-transition source through the source-equivalence source.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtTargetEqInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      payload)

/--
The local transition normal form closes the local restricted-transition source:
the modeled transition is a transported-atlas transition, hence belongs to the
groupoid after restricting to the local open set.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd x hx
  rcases payload e hc hd x hx with ⟨s, hs, hxs, t, ht, hEq⟩
  refine ⟨s, hs, hxs, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  have hSmooth : IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedSmoothabilityBridgePayload e
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := hSmooth
  have hTransported :
      t.symm ≫ₕ d ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
    HasGroupoid.compatible ht hd
  have hRestr :
      (t.symm ≫ₕ d).restr s ∈
        contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
    closedUnderRestriction' hTransported hs
  rw [hEq]
  exact hRestr

/--
The inverse-chart normal form closes the local restricted-transition source via
the accepted transition-model source.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
    (onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedAtlasModel
      payload)

/--
The canonical transported `chartAt` inverse model closes the local
restricted-transition source through the accepted inverse-atlas model.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtModel
      payload)

/--
The local restricted-transition source closes the forward cross-atlas
transition payload by structure-groupoid locality.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  exact StructureGroupoid.locality
    (contDiffGroupoid 1 ThreeManifoldModelWithCorners)
    (payload e hc hd)

/--
The local transition normal-form source also closes the forward cross-atlas
transition payload.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
      payload)

/--
The inverse-chart normal form also closes the forward cross-atlas transition
payload.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
    (onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedAtlasModel
      payload)

/--
The canonical transported `chartAt` inverse model also closes the forward
cross-atlas transition payload.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
    (onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      payload)

/--
The local source-equivalence inverse model closes the forward cross-atlas
transition payload.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
      payload)

/--
The unfolded local target/source and inverse-map identities close the forward
cross-atlas transition payload through the source-equivalence source.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtTargetEqInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      payload)

/--
The two-sided cross-atlas payload projects to its forward local transition
theorem.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  exact (payload e hc hd).1

/--
The forward local transition theorem supplies the two-sided cross-atlas
payload, since structure groupoids are closed under inverses.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  have hForward :
      c.symm ≫ₕ d ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
    payload e hc hd
  have hReverse :
      d.symm ≫ₕ c ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners := by
    have hSymm :
        (c.symm ≫ₕ d).symm ∈
          contDiffGroupoid 1 ThreeManifoldModelWithCorners :=
      StructureGroupoid.symm
        (contDiffGroupoid 1 ThreeManifoldModelWithCorners) hForward
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using hSymm
  exact ⟨hForward, hReverse⟩

/--
The two-sided cross-atlas payload is equivalent to the forward transition
payload.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_iff_forwardChartTransportedAtlasCompatibility :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} ↔
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} :=
  ⟨onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility,
    onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility⟩

/--
If the ambient atlas is the transported one-point atlas, the already-proved
transported smooth manifold structure supplies the cross-atlas compatibility.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  have hAtlas :
      @atlas ThreeManifoldModel _ M _ _charted =
        @atlas ThreeManifoldModel _ M _
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e
  have hcTransported :
      c ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) := by
    rw [← hAtlas]
    exact hc
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  have hSmooth : IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedSmoothabilityBridgePayload e
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := hSmooth
  exact ⟨HasGroupoid.compatible hcTransported hd,
    HasGroupoid.compatible hd hcTransported⟩

/--
For the transported charted-space witness from `SmoothabilityOnePointRecognition`,
the cross-atlas compatibility needed by the bridge follows from the transported
smooth manifold structure.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibility_on_transportedChartedSpace
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) :
    letI : ChartedSpace ThreeManifoldModel M :=
      homeomorphToOnePoint_threeSpace_smoothChartedSpace e
    ∀ {c d : OpenPartialHomeomorph M ThreeManifoldModel},
      c ∈ atlas ThreeManifoldModel M →
      d ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
        c.symm ≫ₕ d ∈
          contDiffGroupoid 1 ThreeManifoldModelWithCorners ∧
        d.symm ≫ₕ c ∈
          contDiffGroupoid 1 ThreeManifoldModelWithCorners := by
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  intro c d hc hd
  have hSmooth : IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedSmoothabilityBridgePayload e
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := hSmooth
  exact ⟨HasGroupoid.compatible hc hd, HasGroupoid.compatible hd hc⟩

/--
If every ambient chart is already a chart of the transported one-point atlas,
then the forward cross-atlas transition is an internal transported-atlas
transition.  This avoids the false requirement that `chartAt p` choose an
arbitrary atlas chart containing `p`.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartInTransportedAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  have hcTransported :
      c ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) :=
    payload e hc
  letI : ChartedSpace ThreeManifoldModel M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  have hSmooth : IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedSmoothabilityBridgePayload e
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := hSmooth
  exact HasGroupoid.compatible hcTransported hd

/--
The same ambient-chart membership source gives the two-sided cross-atlas
compatibility by the existing forward/reverse equivalence.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_chartInTransportedAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartInTransportedAtlas
      payload)

/--
Full charted-space compatibility is therefore strong enough to close the
cross-atlas compatibility payload.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibility
    (onePointRecognitionAmbientAtlasCompatibilityPayload_of_chartedSpaceCompatibility
      compat)

/--
Cross-atlas transition compatibility is exactly the local data needed to put
each ambient chart in the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c hc
  change
    ∀ d ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e),
      c.symm ≫ₕ d ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners ∧
        d.symm ≫ₕ c ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners
  intro d hd
  exact payload e hc hd

/--
The one-directional forward cross-atlas transition theorem is enough to put
each ambient chart in the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
      payload)

/--
The local restricted-transition source is enough to put each ambient chart in
the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localForwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
      payload)

/--
The local transition normal-form source is enough to put each ambient chart in
the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localForwardTransportedAtlasTransitionModel
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
      payload)

/--
The inverse-chart normal form is enough to put each ambient chart in the
transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedAtlasModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
      payload)

/--
The canonical transported `chartAt` inverse model is enough to put each
ambient chart in the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedAtlasModel
    (onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      payload)

/--
The local source-equivalence inverse model is enough to put each ambient chart
in the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedChartAtEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
      payload)

/--
The unfolded local target/source and inverse-map identities are enough to put
each ambient chart in the transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedChartAtTargetEqInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_localInverseTransportedChartAtEqOnSource
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      payload)

/--
Conversely, pointwise transported maximal-atlas membership unfolds to the
cross-atlas compatibility payload.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_chartInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e c d hc hd
  have hChart := payload e hc
  change
    ∀ d ∈ @atlas ThreeManifoldModel _ M _
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e),
      c.symm ≫ₕ d ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners ∧
        d.symm ≫ₕ c ∈ contDiffGroupoid 1 ThreeManifoldModelWithCorners at hChart
  exact hChart d hd

/--
The current pointwise chart-membership blocker is therefore sharpened to the
missing cross-atlas transition compatibility theorem.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_currently_blocked_at_chartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} →
      False := by
  intro payload
  exact compatibilityUnavailable
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_chartInTransportedMaximalAtlas
      payload)

/--
The current pointwise chart-membership blocker can be sharpened further to the
single forward cross-atlas transition theorem.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_currently_blocked_at_forwardChartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} →
      False := by
  intro payload
  exact compatibilityUnavailable
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility
      (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_chartInTransportedMaximalAtlas
        payload))

/--
The raw groupoid-level blocker underneath the transfer theorem: the ambient
atlas transitions themselves must be `C¹` for the surgery model.
-/
def OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
          ThreeManifoldModelWithCorners 1 M inferInstance
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
        ∀ {c c' : OpenPartialHomeomorph M ThreeManifoldModel},
          c ∈ atlas ThreeManifoldModel M →
          c' ∈ atlas ThreeManifoldModel M →
            c.symm ≫ₕ c' ∈
              contDiffGroupoid 1 ThreeManifoldModelWithCorners

/--
The ambient atlas transition payload is exactly the `HasGroupoid` constructor
content needed to transfer from the transported charted space to the ambient
charted-space instance.
-/
def OnePointRecognitionTransportedToAmbientHasGroupoidTransferPayload : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      (e : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3))) →
        @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
          ThreeManifoldModelWithCorners 1 M inferInstance
          (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) →
        HasGroupoid M (contDiffGroupoid 1 ThreeManifoldModelWithCorners)

/--
The comparison datum converts the already-available transported one-point
smoothability bridge into the ambient payload.
-/
theorem onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceComparison
    (comparison :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u}) :
    OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} := by
  intro M _top _t2 _charted _simple _compact h
  rcases h with ⟨e⟩
  exact comparison e (onePointRecognitionTransportedSmoothabilityBridgePayload e)

/--
The charted-space comparison payload is exactly enough to construct the
theorem-shaped smoothability bridge.
-/
theorem smoothabilityBridgeStatement_of_onePointRecognitionAmbientChartedSpaceComparison
    (comparison :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  smoothabilityBridgeStatement_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceComparison
      comparison)

/--
If the ambient atlas is contained in the transported smooth maximal atlas, the
transported `IsManifold` evidence transfers to the ambient charted-space
instance by rebuilding the ambient `HasGroupoid` from maximal-atlas
compatibility.
-/
theorem onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientAtlasInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e _transported
  have hSubset := payload e
  haveI : HasGroupoid M (contDiffGroupoid 1 ThreeManifoldModelWithCorners) := by
    refine ⟨?_⟩
    intro c c' hc hc'
    exact @IsManifold.compatible_of_mem_maximalAtlas ℝ _
      ThreeManifoldModel _ _ ThreeManifoldModel _
      ThreeManifoldModelWithCorners 1 M _top
      (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) c c'
      (hSubset hc) (hSubset hc')
  exact IsManifold.mk' ThreeManifoldModelWithCorners 1 M

/--
Ambient atlas containment in the transported maximal atlas directly supplies
the raw ambient transition compatibility payload.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_ambientAtlasInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e _transported c c' hc hc'
  have hSubset := payload e
  exact @IsManifold.compatible_of_mem_maximalAtlas ℝ _
    ThreeManifoldModel _ _ ThreeManifoldModel _
    ThreeManifoldModelWithCorners 1 M _top
    (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) c c'
    (hSubset hc) (hSubset hc')

/--
The pointwise chart-membership datum is therefore enough to construct the raw
ambient transition-compatibility payload.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_ambientAtlasInTransportedMaximalAtlas
    (onePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload_of_chartInTransportedMaximalAtlas
      payload)

/--
The cross-atlas compatibility payload is also enough to construct raw ambient
atlas transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartInTransportedMaximalAtlas
    (onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
      payload)

/--
The one-directional forward cross-atlas transition theorem is enough to
construct raw ambient atlas transition compatibility through the transported
maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartInTransportedMaximalAtlas
    (onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
      payload)

/--
The local restricted-transition source is enough to construct raw ambient atlas
transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
      payload)

/--
The local transition normal-form source is enough to construct raw ambient
atlas transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
      payload)

/--
The inverse-chart normal form is enough to construct raw ambient atlas
transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedAtlasModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
      payload)

/--
The canonical transported `chartAt` inverse model is enough to construct raw
ambient atlas transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedChartAtModel
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedAtlasModel
    (onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      payload)

/--
The local source-equivalence inverse model is enough to construct raw ambient
atlas transition compatibility through the transported maximal atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
      payload)

/--
The unfolded local target/source and inverse-map identities are enough to
construct raw ambient atlas transition compatibility.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedChartAtTargetEqInvEq
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      payload)

/--
Atlas-level compatibility is enough to construct raw ambient transition
compatibility through the transported smooth atlas.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_ambientAtlasCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibility
      payload)

/--
The ambient transition compatibility payload is the lower-level datum needed to
build the ambient `HasGroupoid` instance.
-/
theorem onePointRecognitionTransportedToAmbientHasGroupoidTransferPayload_of_atlasTransitionCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u}) :
    OnePointRecognitionTransportedToAmbientHasGroupoidTransferPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e transported
  exact ⟨fun hc hc' => payload e transported hc hc'⟩

/--
The groupoid transfer payload closes the current transported-to-ambient
`IsManifold` transfer theorem via `IsManifold.mk'`.
-/
theorem onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_hasGroupoidTransfer
    (payload :
      OnePointRecognitionTransportedToAmbientHasGroupoidTransferPayload.{u}) :
    OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} := by
  intro M _top _t2 _charted _simple _compact e transported
  haveI : HasGroupoid M (contDiffGroupoid 1 ThreeManifoldModelWithCorners) :=
    payload e transported
  exact IsManifold.mk' ThreeManifoldModelWithCorners 1 M

/--
Equivalently, the raw ambient transition compatibility payload closes the
current transfer theorem.
-/
theorem onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_atlasTransitionCompatibility
    (payload :
      OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u}) :
    OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} :=
  onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_hasGroupoidTransfer
    (onePointRecognitionTransportedToAmbientHasGroupoidTransferPayload_of_atlasTransitionCompatibility
      payload)

/--
The transported maximal-atlas containment theorem is therefore sufficient to
construct the theorem-shaped smoothability bridge.
-/
theorem smoothabilityBridgeStatement_of_onePointRecognitionAmbientAtlasInTransportedMaximalAtlas
    (payload :
      OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  smoothabilityBridgeStatement_of_onePointRecognitionAmbientChartedSpaceComparison
    (onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientAtlasInTransportedMaximalAtlas
      payload)

/--
Conversely, the ambient payload is exactly strong enough to provide the
transported-to-ambient comparison.
-/
theorem onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientSmoothabilityBridgePayload
    (payload :
      OnePointRecognitionAmbientSmoothabilityBridgePayload.{u}) :
    OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e _transported
  exact payload ⟨e⟩

/--
The ambient payload is equivalent to the charted-space comparison from the
transported one-point atlas to the ambient charted-space instance.
-/
theorem onePointRecognitionAmbientSmoothabilityBridgePayload_iff_chartedSpaceComparison :
    OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} ↔
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} :=
  ⟨onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientSmoothabilityBridgePayload,
    onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceComparison⟩

/--
The stronger charted-space equality payload supplies the exact comparison
datum by rewriting the hidden charted-space argument of `IsManifold`.
-/
theorem onePointRecognitionAmbientChartedSpaceComparisonPayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e hSmooth
  have hEq :
      _charted = homeomorphToOnePoint_threeSpace_smoothChartedSpace e :=
    compat e
  have hProp :
      @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
        ThreeManifoldModelWithCorners 1 M _top
        (homeomorphToOnePoint_threeSpace_smoothChartedSpace e) =
      @IsManifold ℝ _ ThreeManifoldModel _ _ ThreeManifoldModel _
        ThreeManifoldModelWithCorners 1 M _top _charted := by
    rw [hEq]
  exact Eq.mp hProp hSmooth

/--
Ambient charted-space compatibility converts the transported one-point smooth
manifold theorem into the exact ambient `IsManifold` payload required above.
-/
theorem onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} := by
  exact onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceComparison
    (onePointRecognitionAmbientChartedSpaceComparisonPayload_of_chartedSpaceCompatibility
      compat)

/--
The charted-space compatibility payload is therefore sufficient to construct
the theorem-shaped smoothability bridge.
-/
theorem smoothabilityBridgeStatement_of_onePointRecognitionAmbientChartedSpaceCompatibility
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    SmoothabilityBridgeStatement.{u} :=
  smoothabilityBridgeStatement_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceCompatibility
      compat)

/-- The smoothability package fields through the theorem-shaped bridge. -/
structure SmoothabilityPackageBridgeFields extends
    SmoothabilityPackageSmoothStructureDerivationFields.{u} where
  bridge : SmoothabilityBridgeStatement.{u}

/--
Uniform one-point recognition plus the exact ambient smoothability payload
constructs the package fields through the theorem-shaped bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientSmoothabilityBridgePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} where
  toSmoothabilityPackageSmoothStructureDerivationFields :=
    smoothabilityPackageSmoothStructureDerivationFields_of_onePointRecognition
      recognize
  bridge :=
    smoothabilityBridgeStatement_of_onePointRecognitionAmbientSmoothabilityBridgePayload
      payload

/--
Equivalently, ambient compatibility with the transported one-point charted
space constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartedSpaceCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    recognize
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceCompatibility
      compat)

/--
Uniform one-point recognition plus the exact transported-to-ambient
charted-space comparison constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartedSpaceComparison
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (comparison :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientSmoothabilityBridgePayload
    recognize
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_chartedSpaceComparison
      comparison)

/--
Uniform one-point recognition plus the ambient-in-transported-maximal-atlas
theorem constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasInTransportedMaximalAtlas
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartedSpaceComparison
    recognize
    (onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientAtlasInTransportedMaximalAtlas
      payload)

/--
Uniform one-point recognition plus raw ambient atlas transition compatibility
constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasTransitionCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartedSpaceComparison
    recognize
    (onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_atlasTransitionCompatibility
      payload)

/--
Uniform one-point recognition plus pointwise membership of each ambient chart
in the transported maximal atlas constructs the package fields through the
bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedMaximalAtlas
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasInTransportedMaximalAtlas
    recognize
    (onePointRecognitionAmbientAtlasInTransportedMaximalAtlasPayload_of_chartInTransportedMaximalAtlas
      payload)

/--
Uniform one-point recognition plus cross-atlas compatibility constructs the
package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartTransportedAtlasCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedMaximalAtlas
    recognize
    (onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
      payload)

/--
Uniform one-point recognition plus the one-directional forward cross-atlas
transition theorem constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedMaximalAtlas
    recognize
    (onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_forwardChartTransportedAtlasCompatibility
      payload)

/--
Uniform one-point recognition plus ambient-chart membership in the transported
atlas constructs the package fields through the forward cross-atlas route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartInTransportedAtlas
      payload)

/--
Uniform one-point recognition plus the one-sided ambient-atlas inclusion into
the transported atlas constructs the package fields through the same forward
cross-atlas route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlas_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientChartInTransportedAtlasPayload_of_ambientAtlasSubsetTransportedAtlas
      payload)

/--
The core forward transported-atlas inclusion alone is enough for the current
smoothability route; the reverse inclusion of the transported atlas back into
the ambient atlas is not needed for forward cross-atlas compatibility.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlasCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlas_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_ambientAtlasSubsetTransportedAtlasCore
      payload)

/--
The core transported-`chartAt` generator source constructs the package fields
through the current one-sided transported-atlas inclusion route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlasCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload_of_generatedByTransportedChartAtCore
      generated)

/--
Generation by the ambient `chartAt` selector plus selected-chart compatibility
constructs the current package fields through the transported generator route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_generatedByAmbientChartAtCore_and_chartAtCompatibilityCore
      generated chartAtCompat)

/--
Ambient `chartAt` generation plus pointwise selected-chart compatibility
constructs the package fields through the transported generator route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtCompatibilityCore_via_forwardCompatibility
    recognize generated
    (onePointRecognitionAmbientChartAtCompatibilityCorePayload_of_pointwiseCompatibilityCore
      chartAtCompat)

/--
Replacing the ambient generator source by the exact atlas/range equality gives
the same current forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_eqAmbientChartAtRangeCore
      eqRange)
    chartAtCompat

/--
The exact one-sided ambient atlas inclusion into the ambient `chartAt` range is
the smallest current selector-generation source needed by the pointwise route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (subsetRange :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} := by
  have hGenerated :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} := by
    intro M _top _charted c hc
    rcases subsetRange hc with ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  exact
    smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    recognize
    hGenerated
    chartAtCompat

/--
The source-pointed ambient selector-generation payload is enough for the same
current package route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_selectedByAmbientChartAtOnSourceCore
      selected)
    chartAtCompat

/--
The direct transported source-pointed selector-generation payload constructs the
package fields through the same transported `chartAt` generator route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload_of_selectedByTransportedChartAtOnSourceCore
      selected)

/--
The constructor-level source-pointed transported local-inverse generator payload
constructs the package fields through the transported `chartAt` route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_selectedByTransportedLocalInverseChartOnSourceCore
      selected)

/--
The source-pointed selector route can be supplied by separate source-existence
and selector-choice facts for ambient atlas charts.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasChartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (selects :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload_of_chartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore
      sourcePoint selects)
    chartAtCompat

/--
The current package route only needs ambient/transported selected-chart
compatibility at the selected source points used to generate ambient atlas
charts.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasChartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore_and_selectedSourceCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (selects :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u})
    (selectedCompat :
      OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_chartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore_and_selectedSourceCompatibilityCore
      sourcePoint selects selectedCompat)

/--
Uniform one-point recognition plus the generator-level transported-chartAt
source constructs the package fields through the same one-sided atlas inclusion
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAt_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlas_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSubsetTransportedAtlasPayload_of_generatedByTransportedChartAt
      generated)

/--
The constructor-level local-inverse chart generator source also constructs the
package fields through the one-sided atlas inclusion route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChart_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (generated :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAt_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload_of_generatedByTransportedLocalInverseChart
      generated)

/--
The field-level local-inverse generator range equality constructs the package
fields through the one-sided atlas inclusion route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRange_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (eqRange :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChart_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload_of_eqTransportedLocalInverseChartRange
      eqRange)

/--
The core atlas-field local-inverse generator range comparison constructs the
package fields through the current one-sided atlas inclusion route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (core :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRange_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload_of_core
      core)

/--
The ambient selected-chart source route plus atlas/range equality recovers the
exact transported local-inverse range equality, then uses the existing
forward-compatibility package bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCore_and_eqAmbientChartAtRangeCore_and_chartAtCompatibilityCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (selected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u})
    (eqRange :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u})
    (chartAtCompat :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_selectedByAmbientChartAtOnSourceCore_and_eqAmbientChartAtRangeCore_and_chartAtCompatibilityCore
      selected eqRange chartAtCompat)

/--
The two core atlas-range inclusion directions construct the package fields
through the current one-sided atlas inclusion route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCore_and_rangeSubsetAmbientAtlasCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (ambientSubset :
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u})
    (rangeSubset :
      OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload_of_subset_and_rangeSubset
      ambientSubset rangeSubset)

/--
The source-conditioned split of the forward local-inverse range inclusion
constructs the package fields without needing the reverse range inclusion.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasChartSourcePoint_and_sourceNonemptySubsetTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (sourcePoint :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u})
    (sourceNonemptyRange :
      OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCore_via_forwardCompatibility
    recognize
    (onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload_of_subsetTransportedLocalInverseChartRangeCore
      (onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_chartSourcePoint_and_sourceNonemptySubsetTransportedLocalInverseChartRangeCore
        sourcePoint sourceNonemptyRange))

/--
Uniform one-point recognition plus the local restricted-transition source
constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
      payload)

/--
Uniform one-point recognition plus the local transition normal-form source
constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModel
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
      payload)

/--
Uniform one-point recognition plus the inverse-chart normal form constructs
the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedAtlasModel
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedAtlasModel
      payload)

/--
Uniform one-point recognition plus the canonical transported `chartAt` inverse
model constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedChartAtModel
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedAtlasModel
    recognize
    (onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      payload)

/--
Uniform one-point recognition plus the local source-equivalence inverse model
constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
      payload)

/--
Uniform one-point recognition plus the unfolded local target/source and
inverse-map identities constructs the package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSource
    recognize
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      payload)

/--
Uniform one-point recognition plus the manifold-side local source-intersection
and forward-chart equality germ constructs the package fields through the
existing target/inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEq
    recognize
    (onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
      payload)

/--
Uniform one-point recognition plus the restricted-chart source-equivalence germ
constructs the package fields through the existing manifold-side chart-germ
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEqOnSource
      payload)

/--
Uniform one-point recognition plus local forward-map agreement constructs the
package fields through the restricted-chart source-equivalence route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSource
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
      payload)

/--
Uniform one-point recognition plus the source-restricted chart germ constructs
the package fields through the local forward-map agreement route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSource
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      payload)

/--
Uniform one-point recognition plus common-source chart-germ equality constructs
the package fields through the accepted source-germ route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceGermEq
      payload)

/--
Uniform one-point recognition plus model-side transition identity constructs
the package fields through the common-source chart-germ route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionId
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)

/--
Uniform one-point recognition plus chart-map agreement on the transition source
constructs the package fields through the model-side transition-identity route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionId
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)

/--
Uniform one-point recognition plus right-inverse behavior on the transition
source constructs the package fields through the transition-source chart-map
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInv
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)

/--
Uniform one-point recognition plus target membership and inverse equality on the
actual transition source constructs the package fields through the
transition-source right-inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInv
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
Uniform one-point recognition plus point target membership and common-target
inverse source/chart facts constructs the package fields through the
transition-source split route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonTargetSymmSource_and_commonTargetSymmChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointTargetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u})
    (commonTargetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u})
    (commonTargetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      pointTargetMem)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
      commonTargetSymmSource commonTargetSymmChartEq)

/--
Uniform one-point recognition plus point target membership and selected-target
inverse source/chart facts constructs the package fields through the
transition-source split route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointTargetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u})
    (targetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u})
    (targetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      pointTargetMem)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
      targetSymmSource targetSymmChartEq)

/--
Uniform one-point recognition plus pointwise chart equality and selected-target
source-inclusion/chart-map facts constructs the package fields through the
selected-target split route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEq_and_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u})
    (targetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u})
    (targetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
      pointChartEq)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonSourceTransitionTargetSymmSourceInclusion
      targetSymmSourceInclusion)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource
      targetSymmSourceInclusion targetSymmChartMapEqOnSource)

/--
Uniform one-point recognition plus pointwise chart equality and the lower
common-target source-inclusion/chart-map facts constructs the package fields
through the point-target/common-target route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEq_and_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u})
    (commonTargetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u})
    (commonTargetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonTargetSymmSource_and_commonTargetSymmChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
      pointChartEq)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload_of_commonTargetSymmSourceInclusion
      commonTargetSymmSourceInclusion)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload_of_commonTargetSymmChartMapEq
      (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload_of_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
        commonTargetSymmSourceInclusion
        commonTargetSymmChartMapEqOnSource))

/--
Uniform one-point recognition plus model-target transition identity constructs
the package fields through the accepted model-side transition-identity route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionId
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionId
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonTargetTransitionId
      payload)

/--
Uniform one-point recognition plus explicit chart-map agreement on the
transition source constructs the package fields through the accepted
model-target transition route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionId
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload_of_localTransportedChartAtTargetPreimageChartMapEq
      payload)

/--
Uniform one-point recognition plus the target-preimage right-inverse source
constructs the package fields through the accepted chart-map agreement route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInv
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload_of_localTransportedChartAtTargetPreimageRightInv
      payload)

/--
Uniform one-point recognition plus target-preimage target membership and inverse
equality constructs the package fields through the accepted right-inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInv
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload_of_localTransportedChartAtTargetPreimageTargetInvEq
      payload)

/--
Uniform one-point recognition plus the split target-membership and inverse-map
sources constructs the package fields through the accepted target/inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMem_and_invEqOnTarget
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload_of_targetPreimageTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
Uniform one-point recognition plus local target/source equivalence and
common-target inverse equality constructs the package fields through the split
target-preimage route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIff_and_commonTargetInvEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetSourceIff :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload.{u})
    (commonTargetInvEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMem_and_invEqOnTarget
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetSourceIff
      targetSourceIff)
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload_of_commonTargetInvEq
      commonTargetInvEq)

/--
Uniform one-point recognition plus one-sided target membership and the
common-target forward inverse source constructs the package fields through the
target/source route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSourceChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (commonTargetSymmSourceChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} := by
  have commonTargetInvEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u} :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload_of_commonTargetSymmSourceChartEq
      commonTargetSymmSourceChartEq
  exact
    smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIff_and_commonTargetInvEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload_of_targetPreimageTargetMem_and_commonTargetInvEq
      targetMem commonTargetInvEq)
    commonTargetInvEq

/--
Uniform one-point recognition plus one-sided target membership and the split
common-target transported inverse facts constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSource_and_commonTargetSymmChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (commonTargetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u})
    (commonTargetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSourceChartEq
    recognize
    targetMem
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
      commonTargetSymmSource commonTargetSymmChartEq)

/--
Uniform one-point recognition plus one-sided target membership and the deeper
common-target source-inclusion/chart-map facts constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u})
    (commonTargetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u})
    (commonTargetSymmChartMapEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSource_and_commonTargetSymmChartEq
    recognize
    targetMem
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload_of_commonTargetSymmSourceInclusion
      commonTargetSymmSourceInclusion)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload_of_commonTargetSymmChartMapEq
      commonTargetSymmChartMapEq)

/--
Uniform one-point recognition plus target-preimage chart-map agreement,
common-target source inclusion, and conditional common-target chart-map
agreement constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (commonTargetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u})
    (commonTargetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetMem_and_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetPreimageChartMapEqOnSource
      targetPreimageChartMapEqOnSource)
    commonTargetSymmSourceInclusion
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload_of_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
      commonTargetSymmSourceInclusion commonTargetSymmChartMapEqOnSource)

/--
Uniform one-point recognition plus target-preimage chart-map agreement and
common-target transported inverse convergence constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (commonTargetSymmTendsto :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
    recognize
    targetPreimageChartMapEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_commonTargetSymmTendsto
      commonTargetSymmTendsto)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
      targetPreimageChartMapEqOnSource commonTargetSymmTendsto)

/--
Uniform one-point recognition plus target-preimage chart-map agreement and
pointwise chart equality constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_pointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
    recognize
    targetPreimageChartMapEqOnSource
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
      pointChartEq)

/--
Uniform one-point recognition plus common-source transition identity constructs
the package fields through the current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionId_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_pointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      payload)

/--
Uniform one-point recognition plus transition-source chart-map agreement
constructs the package fields through the current target-preimage/point-equality
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_pointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      payload)

/--
Uniform one-point recognition plus transition-source right-inverse behavior
constructs the package fields through the current target-preimage/point-equality
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInv_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_pointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      payload)

/--
Uniform one-point recognition plus the split transition-source target-membership
and inverse-equality facts constructs the package fields through the current
target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInv_via_targetPreimagePointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      targetMem invEqOnTarget)

/--
Uniform one-point recognition plus point target membership and selected-target
inverse source/chart facts constructs the package fields through the current
target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointTargetMem :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u})
    (targetSymmSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u})
    (targetSymmChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget_via_targetPreimagePointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      pointTargetMem)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
      targetSymmSource targetSymmChartEq)

/--
Uniform one-point recognition plus pointwise chart equality and selected-target
source-inclusion/chart-map facts constructs the package fields through the
current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEq_and_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u})
    (targetSymmSourceInclusion :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u})
    (targetSymmChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMem_and_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq_via_targetPreimagePointChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
      pointChartEq)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonSourceTransitionTargetSymmSourceInclusion
      targetSymmSourceInclusion)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource
      targetSymmSourceInclusion targetSymmChartMapEqOnSource)

/--
Target-preimage chart-map agreement plus pointwise chart equality supplies the
selected-target lower route through the current target-preimage/point-equality
payload route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource_and_pointChartEq_via_commonSourceTransitionTarget
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u})
    (pointChartEq :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEq_and_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource_via_targetPreimagePointChartEq
    recognize pointChartEq
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_pointChartEq
      pointChartEq)
    (onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
      targetPreimageChartMapEqOnSource pointChartEq)

/--
Uniform one-point recognition plus the local restriction-equality chart germ
constructs the package fields through the existing manifold-side chart-germ
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtRestrEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEq
    recognize
    (onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEq
      payload)

/--
Uniform one-point recognition plus atlas-level compatibility constructs the
package fields through the bridge.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartTransportedAtlasCompatibility
    recognize
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibility
      payload)

/--
Honest API boundary for the one-point smoothability bridge: the recognition
theorem is not enough by itself because the ambient charted-space instance is
externally supplied.  The bridge also needs an explicit atlas comparison with
the transported one-point charted space.
-/
structure OnePointRecognitionAmbientAtlasCompatibleBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasCompatibility :
    OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}

/--
Generator-level bridge-input API for the one-sided atlas route: it records that
ambient atlas charts are actual selected charts of the transported one-point
charted-space construction.
-/
structure OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasGeneratedByTransportedChartAt :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u}

/--
Lower generator-level bridge-input API: the ambient atlas charts are identified
with the explicit local-inverse charts that generate the transported
one-point charted-space atlas.
-/
structure OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasGeneratedByTransportedLocalInverseChart :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload.{u}

/--
Field-level local-inverse generator bridge-input API: the ambient atlas field is
identified with the exact range generated by the transported charted-space
constructor.
-/
structure OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasEqTransportedLocalInverseChartRange :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u}

/--
Core field-level local-inverse generator bridge-input API: the atlas field
comparison is stated without recognition-side typeclass hypotheses.
-/
structure OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasEqTransportedLocalInverseChartRangeCore :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u}

/--
Split core field-level local-inverse generator bridge-input API: it exposes the
two set-inclusion directions needed for the ambient atlas/range equality.
-/
structure OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSubsetTransportedLocalInverseChartRangeCore :
    OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u}
  transportedLocalInverseChartRangeSubsetAmbientAtlasCore :
    OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u}

/--
Source-conditioned split bridge input for the one-sided local-inverse range
route: it separates source nonemptiness of ambient atlas charts from range
membership for source-nonempty charts.
-/
structure OnePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasChartSourcePointCore :
    OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u}
  ambientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCore :
    OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u}

/--
One-sided core transported-atlas bridge input: this is the exact field needed
by the current forward-compatibility route.
-/
structure OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSubsetTransportedAtlasCore :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u}

/--
Core generator bridge input for the one-sided transported-atlas route.
-/
structure OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasGeneratedByTransportedChartAtCore :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u}

/--
Split core generator bridge input: it separates generation of the ambient
atlas by the ambient selector from compatibility of the selected chart fields.
-/
structure OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasGeneratedByAmbientChartAtCore :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u}
  ambientChartAtCompatibilityCore :
    OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u}

/--
Pointwise selected-chart split of the core generator bridge input.
-/
structure OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasGeneratedByAmbientChartAtCore :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u}
  ambientChartAtPointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}

/--
Narrower pointwise selected-chart bridge input: the ambient atlas-generation
field is expressed as equality with the ambient `chartAt` range.
-/
structure OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasEqAmbientChartAtRangeCore :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u}
  ambientChartAtPointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}

/--
Smallest current selector-generation split bridge input: the missing ambient
selector fact is the one-sided inclusion into the ambient `chartAt` range; the
reverse inclusion is closed by `chart_mem_atlas`.
-/
structure OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSubsetAmbientChartAtRangeCore :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u}
  ambientChartAtPointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}

/--
Source-pointed selected-chart split bridge input: it names the exact local
selection invariant below the ambient selector-range inclusion.
-/
structure OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSelectedByAmbientChartAtOnSourceCore :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u}
  ambientChartAtPointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}

/--
Direct source-pointed transported selector bridge input: this names the exact
transported selected-chart generator fact needed by the forward-compatibility
route.
-/
structure OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSelectedByTransportedChartAtOnSourceCore :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u}

/--
Constructor-level source-pointed transported local-inverse chart bridge input:
this exposes the exact generator fact behind the transported selected `chartAt`
route.
-/
structure OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u}

/--
Split source-pointed selector bridge input: it separates source existence for
ambient atlas charts from the `chartAt` selector-choice law on that source.
-/
structure OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasChartSourcePointCore :
    OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u}
  ambientChartAtSelectsAtlasChartOnSourceCore :
    OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u}
  ambientChartAtPointwiseCompatibilityCore :
    OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u}

/--
Selected-source compatibility split bridge input: it replaces global pointwise
ambient/transported selector equality by equality only at the source points
actually used by the ambient atlas generator route.
-/
structure OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientAtlasChartSourcePointCore :
    OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u}
  ambientChartAtSelectsAtlasChartOnSourceCore :
    OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u}
  ambientChartAtSelectedSourceCompatibilityCore :
    OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u}

/--
The explicit bridge-input API supplies the cross-atlas compatibility payload
that was previously the source blocker.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} :=
  onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibility
    inputs.ambientAtlasCompatibility

/--
The explicit bridge-input API supplies ambient charts as members of the
transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_ambientAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
      inputs)

/--
The explicit bridge-input API supplies the raw ambient atlas transition
compatibility payload.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_ambientAtlasCompatibility
    inputs.ambientAtlasCompatibility

/--
This is the buildable production API for the current frontier: once the
ambient-atlas comparison is supplied explicitly, the bridge fields are
constructed without any additional smoothability source data.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasCompatibility
    inputs.recognize
    inputs.ambientAtlasCompatibility

/--
Equivalently, the bridge consumes the exact atlas-compatibility payload owned
by the one-point recognition charted-space surface.
-/
theorem smoothabilityPackageBridgeFields_of_smoothabilityOnePointRecognitionAtlasCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (ambientAtlasCompatibility :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasCompatibleBridgeInputs
    { recognize := recognize
      ambientAtlasCompatibility := ambientAtlasCompatibility }

/--
The generator-level bridge input supplies the current forward-compatibility
package route through the one-sided atlas inclusion.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByTransportedChartAtBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAt_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasGeneratedByTransportedChartAt

/--
The lower local-inverse generator bridge input supplies the current
forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByTransportedLocalInverseChartBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChart_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasGeneratedByTransportedLocalInverseChart

/--
The field-level local-inverse generator range bridge input supplies the current
forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasEqTransportedLocalInverseChartRangeBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRange_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasEqTransportedLocalInverseChartRange

/--
The core field-level local-inverse generator range bridge input supplies the
current forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasEqTransportedLocalInverseChartRangeCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasEqTransportedLocalInverseChartRangeCore

/--
The split core field-level local-inverse generator bridge input supplies the
current forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCore_and_rangeSubsetAmbientAtlasCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasSubsetTransportedLocalInverseChartRangeCore
    inputs.transportedLocalInverseChartRangeSubsetAmbientAtlasCore

/--
The source-conditioned split bridge input supplies the current package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasChartSourcePoint_and_sourceNonemptySubsetTransportedLocalInverseChartRangeCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasChartSourcePointCore
    inputs.ambientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCore

/--
The one-sided core transported-atlas bridge input supplies the current
forward-compatibility package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasSubsetTransportedAtlasCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSubsetTransportedAtlasCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasSubsetTransportedAtlasCore

/--
The core generator bridge input supplies the current forward-compatibility
package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByTransportedChartAtCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasGeneratedByTransportedChartAtCore

/--
The direct source-pointed transported selector bridge input supplies the current
package route through the transported `chartAt` generator.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasSelectedByTransportedChartAtOnSourceCore

/--
The constructor-level source-pointed local-inverse bridge input supplies the
current package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore

/--
The split core generator bridge input supplies the current package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtCompatibilityCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasGeneratedByAmbientChartAtCore
    inputs.ambientChartAtCompatibilityCore

/--
The pointwise selected-chart split bridge input supplies the current package
route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCore_and_chartAtPointwiseCompatibilityCore_via_forwardCompatibility
    inputs.recognize
    inputs.ambientAtlasGeneratedByAmbientChartAtCore
    inputs.ambientChartAtPointwiseCompatibilityCore

/--
The exact ambient atlas/range equality bridge input supplies the previous
ambient `chartAt` generator split input.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_eqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientAtlasGeneratedByAmbientChartAtCore :=
    onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload_of_eqAmbientChartAtRangeCore
      inputs.ambientAtlasEqAmbientChartAtRangeCore
  ambientChartAtPointwiseCompatibilityCore :=
    inputs.ambientChartAtPointwiseCompatibilityCore

/--
The exact ambient atlas/range equality bridge input supplies the current
package route through the pointwise selected-chart split.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_eqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs
      inputs)

/--
The one-sided selected-chart range inclusion bridge input supplies the exact
atlas/range equality bridge input, using the closed reverse inclusion from
`ChartedSpace`.
-/
theorem onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_subsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} := by
  have hEq :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u} := by
    intro M _top _charted
    ext c
    constructor
    · intro hc
      exact inputs.ambientAtlasSubsetAmbientChartAtRangeCore hc
    · intro hc
      exact onePointRecognitionAmbientChartAtRangeSubsetAtlasCorePayload hc
  exact
    { recognize := inputs.recognize
      ambientAtlasEqAmbientChartAtRangeCore :=
        hEq
      ambientChartAtPointwiseCompatibilityCore :=
        inputs.ambientChartAtPointwiseCompatibilityCore }

/--
The one-sided selected-chart range inclusion bridge input supplies the current
package route through the pointwise selected-chart split.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_subsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs
      inputs)

/--
The source-pointed selected-chart bridge input supplies the one-sided
selected-chart range bridge input.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_selectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} := by
  exact
    { recognize := inputs.recognize
      ambientAtlasSubsetAmbientChartAtRangeCore := by
        intro M _top _charted c hc
        rcases inputs.ambientAtlasSelectedByAmbientChartAtOnSourceCore hc with
          ⟨q, _hqSource, hq⟩
        exact ⟨q, hq.symm⟩
      ambientChartAtPointwiseCompatibilityCore :=
        inputs.ambientChartAtPointwiseCompatibilityCore }

/--
The source-pointed selected-chart bridge input supplies the current package
route through the pointwise selected-chart split.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_selectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs
      inputs)

/--
The selected-source compatibility split bridge input supplies the direct
source-pointed transported selector bridge input.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_of_chartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientAtlasSelectedByTransportedChartAtOnSourceCore :=
    onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_chartSourcePoint_and_chartAtSelectsAtlasChartOnSourceCore_and_selectedSourceCompatibilityCore
      inputs.ambientAtlasChartSourcePointCore
      inputs.ambientChartAtSelectsAtlasChartOnSourceCore
      inputs.ambientChartAtSelectedSourceCompatibilityCore

/--
The constructor-level source-pointed local-inverse bridge input supplies the
direct transported selected-`chartAt` bridge input.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_of_selectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientAtlasSelectedByTransportedChartAtOnSourceCore :=
    onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload_of_selectedByTransportedLocalInverseChartOnSourceCore
      inputs.ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore

/--
The existing forward local-inverse range split bridge input supplies the
source-pointed local-inverse bridge input; the reverse range inclusion is not
needed for this one-sided smoothability route.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs_of_eqTransportedLocalInverseChartRangeCoreSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore :=
    onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload_of_subsetTransportedLocalInverseChartRangeCore
      inputs.ambientAtlasSubsetTransportedLocalInverseChartRangeCore

/--
The source-conditioned split bridge input supplies the source-pointed
constructor-level transported local-inverse bridge input.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs_of_chartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore :=
    onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload_of_subsetTransportedLocalInverseChartRangeCore
      (onePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload_of_chartSourcePoint_and_sourceNonemptySubsetTransportedLocalInverseChartRangeCore
        inputs.ambientAtlasChartSourcePointCore
        inputs.ambientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCore)

/--
The split source-pointed selector bridge input supplies the source-pointed
selector bridge input.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_chartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} := by
  have hSelected :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} := by
    intro M _top _charted c hc
    rcases inputs.ambientAtlasChartSourcePointCore hc with ⟨q, hq⟩
    exact ⟨q, hq, inputs.ambientChartAtSelectsAtlasChartOnSourceCore hc hq⟩
  exact
    { recognize := inputs.recognize
      ambientAtlasSelectedByAmbientChartAtOnSourceCore := hSelected
      ambientChartAtPointwiseCompatibilityCore :=
        inputs.ambientChartAtPointwiseCompatibilityCore }

/--
The split source-pointed selector bridge input supplies the current package
route through the pointwise selected-chart split.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_of_chartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs
      inputs)

/--
The selected-source compatibility bridge input supplies the previous
source-pointed selector package route.
-/
theorem smoothabilityPackageBridgeFields_of_ambientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs_via_forwardCompatibility
    (inputs :
      OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_ambientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_via_forwardCompatibility
    (onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_of_chartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs
      inputs)

/--
Narrower honest bridge-input API: instead of identifying the whole arbitrary
ambient atlas with the transported one-point atlas, it asks only for the local
cross-atlas transition compatibility that puts each ambient chart in the
transported smooth maximal atlas.
-/
structure OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartTransportedAtlasCompatibility :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u}

/--
Narrowest current bridge-input API: it asks only for the forward local
transition from each ambient chart to each transported one-point chart.  The
reverse transition is recovered by groupoid inversion.
-/
structure OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartForwardTransportedAtlasCompatibility :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u}

/--
Local-source bridge-input API: it asks only for the local restricted transition
datum that `StructureGroupoid.locality` needs to recover the accepted forward
cross-atlas payload.
-/
structure OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalForwardTransportedAtlasCompatibility :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u}

/--
Sharper local normal-form bridge-input API: it asks for a local equality to a
transition between transported one-point charts, not for direct groupoid
membership of the ambient-to-transported transition.
-/
structure OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalForwardTransportedAtlasTransitionModel :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u}

/--
Sharper inverse-chart bridge-input API: it asks only for local equality between
an ambient chart inverse and a transported one-point chart inverse.
-/
structure OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalInverseTransportedAtlasModel :
    OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u}

/--
Sharper canonical-chart inverse bridge-input API: it fixes the transported
one-point chart witness to the transported `chartAt` at each ambient inverse
point.
-/
structure OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalInverseTransportedChartAtModel :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u}

/--
Weakest current canonical-chart inverse bridge-input API: it asks only for
source-equivalence between the restricted ambient inverse and the transported
`chartAt` inverse.
-/
structure OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalInverseTransportedChartAtEqOnSource :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u}

/--
Unfolded canonical-chart inverse bridge-input API: it asks for local target
equality and inverse-map equality, the two concrete ingredients of the
restricted inverse-chart source-equivalence theorem.
-/
structure OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalInverseTransportedChartAtTargetEqInvEq :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u}

/--
Manifold-side local chart-germ bridge-input API: it asks for local source
intersection equality and forward-chart equality between each ambient chart and
the transported `chartAt` selected at the same source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtSourceEqChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u}

/--
Local restriction-equality chart-germ bridge-input API: it asks for equality of
the restricted ambient chart and transported `chartAt` around each source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtRestrEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u}

/--
Restricted-chart source-equivalence bridge-input API: it asks only for
`EqOnSource` between the restricted ambient chart and transported `chartAt`
around each source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtRestrEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u}

/--
Pointwise local chart-germ bridge-input API: it asks only for local forward-map
agreement between each ambient chart and the transported `chartAt` near each
source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtChartEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u}

/--
Source-restricted chart-germ bridge-input API: it asks for the same local
forward-map agreement, expressed as equality eventually in `𝓝[c.source] p`.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtSourceGermEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u}

/--
Conditional source-germ bridge-input API: it asks only for source-filter
chart-map agreement at points that lie in the transported `chartAt` source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u}

/--
Common-source chart-germ bridge-input API: it asks for equality eventually only
on the common source of the ambient chart and transported `chartAt`.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonSourceGermEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}

/--
Transported-atlas local chart-germ bridge-input API: it separates the accepted
common-source chart-germ payload into ambient chart membership in the transported
atlas and the internal transported-atlas `chartAt` source-germ locality theorem.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtCommonSourceGermEq :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}

/--
Transported-atlas transition-identity bridge-input API: it keeps the ambient
transported-atlas membership side and replaces the internal transported-atlas
chart-map agreement theorem by local identity of the coordinate transition.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionId :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u}

/--
Split transported-atlas transition-identity bridge-input API: it separates
target membership on the actual internal coordinate-transition source from
inverse-map equality on the selected-target restriction of that source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionTargetMem :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}

/--
Point-target/selected-target lower transported-atlas bridge-input API: it
replaces internal transition target membership by point target membership and
splits inverse equality into source inclusion plus conditional chart-map
agreement.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtPointTargetMem :
    OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}

/--
Point-chart/target-preimage lower transported-atlas bridge-input API: it
replaces point target membership by pointwise chart equality and derives the
selected-target source/chart-map fields from the target-preimage chart-map
source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtPointChartEq :
    OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u}
  transportedAtlasChartAtTargetPreimageChartMapEqOnSource :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u}

/--
Target-preimage right-inverse transported-atlas bridge-input API: it isolates
the local identity of the selected transported `chartAt` on the target-preimage
source as the remaining chartAt-choice compatibility fact.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtTargetPreimageRightInv :
    OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u}

/--
Source-side transported-atlas chart-map bridge-input API: it isolates the
chartAt-choice compatibility before pulling back along the transported atlas
chart inverse.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtSourceChartMapEqOnTransportedSource :
    OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u}

/--
ChartAt-choice transported-atlas bridge-input API: it isolates the exact
selected-chart equality needed to recover source-side chart-map compatibility.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtChoosesAtlasChart :
    OnePointRecognitionTransportedAtlasChartAtChoosesAtlasChartPayload.{u}

/--
Transported-atlas transition chart-map bridge-input API: it keeps the ambient
transported-atlas membership side and replaces the internal transported-atlas
common-source germ theorem by chart-map agreement on the actual coordinate
transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartInTransportedAtlas :
    OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u}
  transportedAtlasChartAtCommonSourceTransitionChartMapEq :
    OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u}

/--
Model-side transition-identity bridge-input API: it asks that the coordinate
change from an ambient chart to transported `chartAt` is eventually the identity
on its own source near the represented source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionId :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u}

/--
Transition-source chart-map bridge-input API: it asks only that, on the actual
source of the coordinate transition from an ambient chart to transported
`chartAt`, the transported chart map agrees with the ambient chart map after
`c.symm`.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u}

/--
Transition-source right-inverse bridge-input API: it asks that transported
`chartAt` sends `c.symm z` back to `z` on the actual source of the coordinate
transition.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u}

/--
Split transition-source right-inverse bridge-input API: it separates transported
target membership on the actual transition source from inverse equality on the
target-restricted transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}

/--
Point-target/common-target inverse bridge-input API: it replaces
transition-source target membership with point target membership, and replaces
target-restricted inverse equality with source membership plus chart equality on
the common target.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtPointTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}

/--
Point-target/selected-target inverse bridge-input API: it replaces
transition-source target membership with point target membership, and replaces
target-restricted inverse equality with source membership plus chart equality on
the target-restricted actual transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtPointTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u}

/--
Point-equality/selected-target lower inverse bridge-input API: it replaces point
target membership by pointwise chart equality, replaces selected-target inverse
source membership by source inclusion, and uses conditional chart-map equality
on the same target-restricted transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtPointChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u}
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}

/--
Point-equality/lower common-target bridge-input API: it replaces point target
membership by pointwise chart equality, replaces common-target transported
inverse source membership by source inclusion, and uses the conditional
chart-map equality source on that same common target.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtPointChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}

/--
Model-target transition-identity bridge-input API: it asks that the coordinate
change from an ambient chart to transported `chartAt` is eventually the identity
only on the common target of the ambient chart and transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtCommonTargetTransitionId :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload.{u}

/--
Explicit chart-map bridge-input API: it asks only that the transported
`chartAt` map and ambient chart map agree after applying `c.symm`, on the
explicit transition source in model coordinates.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u}

/--
Target-preimage right-inverse bridge-input API: it asks only that transported
`chartAt` sends `c.symm z` back to `z` on the explicit transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageRightInv :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u}

/--
Target-preimage inverse-map bridge-input API: it asks only for transported
target membership plus inverse-chart equality on the explicit transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageTargetInvEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload.{u}

/--
Split target-preimage bridge-input API: it separates transported target
membership on the transition source from inverse equality on the
target-restricted transition source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtTargetPreimageInvEqOnTarget :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u}

/--
Local target/source bridge-input API: it replaces the broad split facts with
local target/source equivalence and inverse equality on the common target.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetSourceIff :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetInvEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u}

/--
One-sided target-membership bridge-input API: it replaces target/source
equivalence with transported target membership on the explicit transition
source, and replaces inverse equality with the forward inverse source.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload.{u}

/--
Split common-target bridge-input API: it separates the transported inverse
ambient-source membership from the ambient chart equality on the common target.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u}

/--
Deeper common-target bridge-input API: source membership is reduced to a local
source inclusion, and chart equality is reduced to chart-map agreement before
using the transported chart right-inverse law.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload.{u}

/--
Lower chart-map bridge-input API: target membership is reduced to chart-map
agreement on the explicit target-preimage source, while common-target chart-map
agreement is required only after source membership has been isolated.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u}

/--
Tendsto bridge-input API: common-target transported inverse source inclusion
and conditional chart-map agreement are both reduced to convergence of
`t.symm` back to `p` along the common target.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u}
  ambientChartLocalTransportedChartAtCommonTargetSymmTendsto :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u}

/--
Point-equality bridge-input API: common-target transported inverse convergence
is reduced to pointwise agreement of the ambient chart and transported `chartAt`
at the source point.
-/
structure OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs where
  recognize : OnePointThreeSpaceRecognitionStatement.{u}
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u}
  ambientChartLocalTransportedChartAtPointChartEq :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u}

/--
The atlas-equality bridge inputs still supply the narrower cross-atlas
compatibility bridge inputs.
-/
theorem ambientChartTransportedAtlasCompatibleBridgeInputs_of_ambientAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
      inputs

/--
The two-sided cross-atlas bridge inputs supply the one-directional current
frontier input.
-/
theorem ambientChartForwardTransportedAtlasCompatibleBridgeInputs_of_chartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartForwardTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility
      inputs.ambientChartTransportedAtlasCompatibility

/--
The local-source bridge inputs supply the accepted one-directional current
frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardChartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartForwardTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_localForwardChartTransportedAtlasCompatibility
      inputs.ambientChartLocalForwardTransportedAtlasCompatibility

/--
The local transition normal-form bridge inputs supply the accepted local
restricted-transition bridge inputs.
-/
theorem localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardTransportedAtlasTransitionModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalForwardTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localForwardTransportedAtlasTransitionModel
      inputs.ambientChartLocalForwardTransportedAtlasTransitionModel

/--
The inverse-chart normal-form bridge inputs supply the accepted local
transition-model bridge inputs.
-/
theorem localForwardTransportedAtlasTransitionModelBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalForwardTransportedAtlasTransitionModel :=
    onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload_of_localInverseTransportedAtlasModel
      inputs.ambientChartLocalInverseTransportedAtlasModel

/--
The canonical transported `chartAt` inverse bridge inputs supply the accepted
inverse-atlas model bridge inputs.
-/
theorem localInverseTransportedAtlasModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalInverseTransportedAtlasModel :=
    onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload_of_localInverseTransportedChartAtModel
      inputs.ambientChartLocalInverseTransportedChartAtModel

/--
The canonical transported `chartAt` equality bridge inputs supply the weaker
source-equivalence bridge inputs.
-/
theorem localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalInverseTransportedChartAtEqOnSource :=
    onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtModel
      inputs.ambientChartLocalInverseTransportedChartAtModel

/--
The unfolded target/source and inverse-map bridge inputs supply the accepted
source-equivalence bridge inputs.
-/
theorem localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalInverseTransportedChartAtEqOnSource :=
    onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload_of_localInverseTransportedChartAtTargetEqInvEq
      inputs.ambientChartLocalInverseTransportedChartAtTargetEqInvEq

/--
The manifold-side local source-intersection and forward-chart equality bridge
inputs supply the accepted target/inverse bridge inputs.
-/
theorem localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalInverseTransportedChartAtTargetEqInvEq :=
    onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload_of_localTransportedChartAtSourceEqChartEq
      inputs.ambientChartLocalTransportedChartAtSourceEqChartEq

/--
The manifold-side local source-intersection and forward-chart equality bridge
inputs also supply the accepted source-equivalence bridge inputs.
-/
theorem localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u} :=
  localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
      inputs)

/--
The local restriction-equality chart-germ bridge inputs supply the accepted
manifold-side source-intersection and forward-chart equality bridge inputs.
-/
theorem localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtSourceEqChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEq
      inputs.ambientChartLocalTransportedChartAtRestrEq

/--
Full local restriction equality supplies the weaker restricted-chart
source-equivalence bridge inputs.
-/
theorem localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtRestrEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtRestrEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtRestrEq
      inputs.ambientChartLocalTransportedChartAtRestrEq

/--
The restricted-chart source-equivalence bridge inputs supply the accepted
manifold-side source-intersection and forward-chart equality bridge inputs.
-/
theorem localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtSourceEqChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload_of_localTransportedChartAtRestrEqOnSource
      inputs.ambientChartLocalTransportedChartAtRestrEqOnSource

/--
The local forward-map agreement bridge inputs supply restricted-chart
source-equivalence bridge inputs by shrinking to the common chart source.
-/
theorem localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtRestrEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
      inputs.ambientChartLocalTransportedChartAtChartEqOnSource

/--
The local forward-map agreement bridge inputs also supply the accepted
manifold-side source-intersection and forward-chart equality bridge inputs.
-/
theorem localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u} :=
  localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
    (localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
      inputs)

/--
The source-restricted chart-germ bridge inputs supply the local forward-map
agreement bridge inputs by extracting an open neighborhood from the source
germ.
-/
theorem localTransportedChartAtChartEqOnSourceBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtChartEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      inputs.ambientChartLocalTransportedChartAtSourceGermEq

/--
The source-restricted chart-germ bridge inputs also supply restricted-chart
source-equivalence bridge inputs through the local forward-map agreement bridge.
-/
theorem localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u} :=
  localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (localTransportedChartAtChartEqOnSourceBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
      inputs)

/--
The source-restricted chart-germ bridge inputs supply the conditional
transported-source chart-map bridge inputs.
-/
theorem sourceChartMapEqOnTransportedSourceBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload_of_localTransportedChartAtSourceGermEq
      inputs.ambientChartLocalTransportedChartAtSourceGermEq

/--
The common-source chart-germ bridge inputs directly supply the conditional
transported-source chart-map bridge inputs.
-/
theorem sourceChartMapEqOnTransportedSourceBridgeInputs_of_commonSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload_of_commonSourceGermEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceGermEq

/--
The common-source chart-germ bridge inputs supply the accepted source-germ
bridge inputs because the transported `chartAt` source is a neighborhood of the
source point.
-/
theorem localTransportedChartAtSourceGermEqBridgeInputs_of_localTransportedChartAtCommonSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtSourceGermEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload_of_localTransportedChartAtCommonSourceGermEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceGermEq

/--
The model-side transition-identity bridge inputs supply common-source chart-germ
bridge inputs by pulling the identity transition back along the ambient chart.
-/
theorem localTransportedChartAtCommonSourceGermEqBridgeInputs_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceGermEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_localTransportedChartAtCommonSourceTransitionId
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionId

/--
The transported-atlas local chart-germ bridge inputs supply the accepted
common-source chart-germ bridge inputs.
-/
theorem localTransportedChartAtCommonSourceGermEqBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceGermEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload_of_chartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq
      inputs.ambientChartInTransportedAtlas
      inputs.transportedAtlasChartAtCommonSourceGermEq

/--
Internal transported-atlas transition chart-map bridge inputs supply the
transported-atlas common-source germ bridge inputs.
-/
theorem commonSourceTransportedAtlasGermBridgeInputs_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceGermEq :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload_of_transitionChartMapEq
      inputs.transportedAtlasChartAtCommonSourceTransitionChartMapEq

/--
Internal transported-atlas transition identity bridge inputs supply the
transported-atlas transition chart-map bridge inputs.
-/
theorem commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceTransitionChartMapEq :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload_of_transitionId
      inputs.transportedAtlasChartAtCommonSourceTransitionId

/--
Internal transported-atlas transition identity bridge inputs supply the
transported-atlas common-source germ bridge inputs.
-/
theorem commonSourceTransportedAtlasGermBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u} :=
  commonSourceTransportedAtlasGermBridgeInputs_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs
    (commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
      inputs)

/--
Conversely, transported-atlas common-source germ bridge inputs supply the
transition-identity bridge inputs, so the germ frontier is exactly the local
coordinate-transition identity frontier.
-/
theorem commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceTransitionId :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_commonSourceGermEq
      inputs.transportedAtlasChartAtCommonSourceGermEq

/--
Split internal transported-atlas transition facts supply the internal
transported-atlas transition-identity bridge inputs.
-/
theorem commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceTransitionId :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_targetMem_and_invEqOnTarget
      inputs.transportedAtlasChartAtCommonSourceTransitionTargetMem
      inputs.transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget

/--
Point-target membership plus selected-target source inclusion and chart-map
agreement supply the split internal transported-atlas transition facts.
-/
theorem commonSourceTransportedAtlasTransitionIdSplitBridgeInputs_of_commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceTransitionTargetMem :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      inputs.transportedAtlasChartAtPointTargetMem
  transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload_of_targetSymmSourceInclusion_and_targetSymmChartMapEqOnSource
      inputs.transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion
      inputs.transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource

/--
Pointwise chart equality and target-preimage chart-map agreement supply the
point-target/selected-target transported-atlas bridge inputs.
-/
theorem commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtPointTargetMem :=
    onePointRecognitionTransportedAtlasChartAtPointTargetMemPayload_of_pointChartEq
      inputs.transportedAtlasChartAtPointChartEq
  transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_pointChartEq
      inputs.transportedAtlasChartAtPointChartEq
  transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
      inputs.transportedAtlasChartAtTargetPreimageChartMapEqOnSource
      inputs.transportedAtlasChartAtPointChartEq

/--
The target-preimage right-inverse transported-atlas source supplies the
point-chart/target-preimage bridge inputs.
-/
theorem commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtPointChartEq :=
    onePointRecognitionTransportedAtlasChartAtPointChartEqPayload_of_targetPreimageChartMapEqOnSource
      (onePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload_of_targetPreimageRightInv
        inputs.transportedAtlasChartAtTargetPreimageRightInv)
  transportedAtlasChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload_of_targetPreimageRightInv
      inputs.transportedAtlasChartAtTargetPreimageRightInv

/--
The internal transported-atlas common-source germ bridge inputs supply the
target-preimage right-inverse bridge inputs.
-/
theorem commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtTargetPreimageRightInv :=
    onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_commonSourceGermEq
      inputs.transportedAtlasChartAtCommonSourceGermEq

/--
The source-side transported-atlas chart-map bridge inputs supply the
target-preimage right-inverse bridge inputs by pulling the source equality
across the transported atlas chart inverse.
-/
theorem commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_of_commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtTargetPreimageRightInv :=
    onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_sourceChartMapEqOnTransportedSource
      inputs.transportedAtlasChartAtSourceChartMapEqOnTransportedSource

/--
The explicit transported-atlas `chartAt` choice bridge inputs supply the
source-side chart-map bridge inputs.
-/
theorem commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_of_commonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtSourceChartMapEqOnTransportedSource :=
    onePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload_of_chartAtChoosesAtlasChart
      inputs.transportedAtlasChartAtChoosesAtlasChart

/--
The target-preimage right-inverse transported-atlas bridge inputs also supply
the internal transition-identity bridge inputs by restricting to the actual
transition source.
-/
theorem commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtCommonSourceTransitionId :=
    onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_targetPreimageRightInv
      inputs.transportedAtlasChartAtTargetPreimageRightInv

/--
Conversely, internal transition-identity bridge inputs recover the
target-preimage right-inverse bridge inputs through the common-source germ
route.
-/
theorem commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartInTransportedAtlas := inputs.ambientChartInTransportedAtlas
  transportedAtlasChartAtTargetPreimageRightInv :=
    onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_transitionId
      inputs.transportedAtlasChartAtCommonSourceTransitionId

/--
Split internal transported-atlas transition facts supply the internal
transported-atlas transition chart-map bridge inputs.
-/
theorem commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u} :=
  commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
    (commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs
      inputs)

/--
Internal transported-atlas transition chart-map bridge inputs supply the
accepted ambient common-source chart-germ bridge inputs.
-/
theorem localTransportedChartAtCommonSourceGermEqBridgeInputs_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u} :=
  localTransportedChartAtCommonSourceGermEqBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
    (commonSourceTransportedAtlasGermBridgeInputs_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs
      inputs)

/--
The model-target transition-identity bridge inputs supply the accepted
model-side transition-identity bridge inputs by enlarging along the ambient
chart target neighborhood.
-/
theorem localTransportedChartAtCommonSourceTransitionIdBridgeInputs_of_localTransportedChartAtCommonTargetTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionId :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonTargetTransitionId
      inputs.ambientChartLocalTransportedChartAtCommonTargetTransitionId

/--
Transition-source chart-map bridge inputs supply model-side transition-identity
bridge inputs by using the ambient chart right-inverse.
-/
theorem localTransportedChartAtCommonSourceTransitionIdBridgeInputs_of_localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionId :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq

/--
Transition-source right-inverse bridge inputs supply transition-source chart-map
bridge inputs by applying the ambient chart right-inverse.
-/
theorem localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs_of_localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv

/--
The split transition-source right-inverse bridge inputs supply right-inverse
bridge inputs by applying transported chart `right_inv`.
-/
theorem localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs_of_commonSourceTransitionRightInvSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget

/--
Point target membership plus common-target inverse source and chart equality
supply the split transition-source right-inverse bridge inputs.
-/
theorem commonSourceTransitionRightInvSplitBridgeInputs_of_pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      inputs.ambientChartLocalTransportedChartAtPointTargetMem
  ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartEq

/--
Point target membership plus selected-target inverse source and chart equality
supply the split transition-source right-inverse bridge inputs.
-/
theorem commonSourceTransitionRightInvSplitBridgeInputs_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_pointTargetMem
      inputs.ambientChartLocalTransportedChartAtPointTargetMem
  ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_commonSourceTransitionTargetSymmSource_and_commonSourceTransitionTargetSymmChartEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSource
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEq

/--
The broader common-target bridge inputs supply the selected-target bridge inputs
by restricting their common-target inverse facts to the actual transition
source.
-/
theorem pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_of_pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointTargetMem :=
    inputs.ambientChartLocalTransportedChartAtPointTargetMem
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonTargetSymmSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSource
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonTargetSymmChartEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartEq

/--
Pointwise chart equality plus selected-target source-inclusion/chart-map facts
supply the selected-target point-target/source/chart bridge inputs.
-/
theorem pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
      inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload_of_commonSourceTransitionTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload_of_commonSourceTransitionTargetSymmSourceInclusion_and_commonSourceTransitionTargetSymmChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource

/--
The broader common-target lower bridge inputs supply the selected-target lower
bridge inputs by restricting their common-target facts to the actual transition
source.
-/
theorem pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointChartEq :=
    inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_commonTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_commonTargetSymmChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource

/--
The target-preimage chart-map and pointwise chart-equality inputs directly
supply the selected-target lower bridge inputs.
-/
theorem pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointChartEq :=
    inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload_of_pointChartEq
      inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
Pointwise chart equality plus the lower common-target source-inclusion/chart-map
facts supply the accepted point-target/common-target bridge inputs.
-/
theorem pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs_of_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload_of_pointChartEq
      inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonTargetSymmSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload_of_commonTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
  ambientChartLocalTransportedChartAtCommonTargetSymmChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload_of_commonTargetSymmChartMapEq
      (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload_of_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
        inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
        inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource)

/--
The lower target-preimage chart-map and pointwise chart-equality inputs supply
the current point-equality/common-target bridge inputs.
-/
theorem pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtPointChartEq :=
    inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_pointChartEq
      inputs.ambientChartLocalTransportedChartAtPointChartEq
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_pointChartEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
The explicit target-preimage chart-map bridge inputs supply transition-source
chart-map bridge inputs by rewriting the transition source.
-/
theorem localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs_of_localTransportedChartAtTargetPreimageChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload_of_localTransportedChartAtTargetPreimageChartMapEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEq

/--
The explicit target-preimage right-inverse bridge inputs supply source-side
transition right-inverse bridge inputs by rewriting the transition source.
-/
theorem localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs_of_localTransportedChartAtTargetPreimageRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload_of_localTransportedChartAtTargetPreimageRightInv
      inputs.ambientChartLocalTransportedChartAtTargetPreimageRightInv

/--
The target-preimage split bridge inputs supply the transition-source split bridge
inputs by rewriting the actual transition source.
-/
theorem commonSourceTransitionRightInvSplitBridgeInputs_of_targetPreimageTargetInvEqSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload_of_localTransportedChartAtTargetPreimageTargetMem
      inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem
  ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload_of_localTransportedChartAtTargetPreimageInvEqOnTarget
      inputs.ambientChartLocalTransportedChartAtTargetPreimageInvEqOnTarget

/--
The explicit chart-map bridge inputs supply the model-target transition-identity
bridge inputs by unfolding the transition and applying the ambient inverse law.
-/
theorem localTransportedChartAtCommonTargetTransitionIdBridgeInputs_of_localTransportedChartAtTargetPreimageChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtCommonTargetTransitionId :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload_of_localTransportedChartAtTargetPreimageChartMapEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEq

/--
The target-preimage right-inverse bridge inputs supply explicit chart-map
agreement bridge inputs by applying the ambient chart inverse law.
-/
theorem localTransportedChartAtTargetPreimageChartMapEqBridgeInputs_of_localTransportedChartAtTargetPreimageRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload_of_localTransportedChartAtTargetPreimageRightInv
      inputs.ambientChartLocalTransportedChartAtTargetPreimageRightInv

/--
The target-preimage inverse-map bridge inputs supply right-inverse bridge inputs
by rewriting through the transported chart inverse.
-/
theorem localTransportedChartAtTargetPreimageRightInvBridgeInputs_of_localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageRightInv :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload_of_localTransportedChartAtTargetPreimageTargetInvEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetInvEq

/--
The split target-preimage bridge inputs supply the accepted target/inverse
bridge inputs by restricting the inverse equality to the eventual transported
target membership.
-/
theorem localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs_of_targetPreimageTargetInvEqSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageTargetInvEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload_of_targetPreimageTargetMem_and_invEqOnTarget
      inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem
      inputs.ambientChartLocalTransportedChartAtTargetPreimageInvEqOnTarget

/--
The local target/source and common-target inverse bridge inputs supply the split
target-preimage bridge inputs.
-/
theorem targetPreimageTargetInvEqSplitBridgeInputs_of_targetSourceIffCommonTargetInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetSourceIff
      inputs.ambientChartLocalTransportedChartAtTargetSourceIff
  ambientChartLocalTransportedChartAtTargetPreimageInvEqOnTarget :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload_of_commonTargetInvEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetInvEq

/--
The one-sided target-membership bridge inputs supply the local target/source
and common-target inverse bridge inputs.
-/
theorem targetSourceIffCommonTargetInvEqBridgeInputs_of_targetMemCommonTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetSourceIff :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload_of_targetPreimageTargetMem_and_commonTargetInvEq
      inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem
      (onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload_of_commonTargetSymmSourceChartEq
        inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceChartEq)
  ambientChartLocalTransportedChartAtCommonTargetInvEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload_of_commonTargetSymmSourceChartEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceChartEq

/--
The split common-target bridge inputs supply the accepted one-sided
target-membership bridge inputs.
-/
theorem targetMemCommonTargetSymmSourceChartEqBridgeInputs_of_targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :=
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload_of_commonTargetSymmSource_and_commonTargetSymmChartEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartEq

/--
The deeper common-target bridge inputs supply the split common-target bridge
inputs.
-/
theorem targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs_of_targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :=
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem
  ambientChartLocalTransportedChartAtCommonTargetSymmSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload_of_commonTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
  ambientChartLocalTransportedChartAtCommonTargetSymmChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload_of_commonTargetSymmChartMapEq
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEq

/--
The lower chart-map bridge inputs supply the accepted deeper common-target
bridge inputs.
-/
theorem targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs_of_targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageTargetMem :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload_of_targetPreimageChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :=
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload_of_commonTargetSymmSourceInclusion_and_commonTargetSymmChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource

/--
The tendsto bridge inputs supply the lower chart-map bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
  ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload_of_commonTargetSymmTendsto
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmTendsto
  ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload_of_targetPreimageChartMapEqOnSource_and_commonTargetSymmTendsto
      inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
      inputs.ambientChartLocalTransportedChartAtCommonTargetSymmTendsto

/--
The point-equality bridge inputs supply the accepted tendsto bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource
  ambientChartLocalTransportedChartAtCommonTargetSymmTendsto :=
    onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload_of_pointChartEq
      inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
The local forward-map agreement bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtChartEqOnSource
      inputs.ambientChartLocalTransportedChartAtChartEqOnSource
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtChartEqOnSource
      inputs.ambientChartLocalTransportedChartAtChartEqOnSource

/--
The conditional source-germ chart-map bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_sourceChartMapEqOnTransportedSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_sourceChartMapEqOnTransportedSource
      inputs.ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_sourceChartMapEqOnTransportedSource
      inputs.ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource

/--
The source-restricted chart-germ bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtSourceGermEq
      inputs.ambientChartLocalTransportedChartAtSourceGermEq
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtSourceGermEq
      inputs.ambientChartLocalTransportedChartAtSourceGermEq

/--
The common-source chart-germ bridge inputs supply the current point-equality
target-preimage bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_commonSourceGermEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceGermEq
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_commonSourceGermEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceGermEq

/--
The common-source transition-identity bridge inputs supply the current
point-equality target-preimage bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} :=
  targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceGermEqBridgeInputs
    (localTransportedChartAtCommonSourceGermEqBridgeInputs_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
      inputs)

/--
The transition-source chart-map bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionChartMapEq
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq

/--
The transition-source right-inverse bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_localTransportedChartAtCommonSourceTransitionRightInv
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv

/--
The split transition-source right-inverse bridge inputs supply the current
target-preimage/point-equality bridge inputs.
-/
theorem targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionRightInvSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource :=
    onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget
  ambientChartLocalTransportedChartAtPointChartEq :=
    onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload_of_commonSourceTransitionTargetMem_and_invEqOnTarget
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem
      inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget

/--
The local restriction-equality chart-germ bridge inputs also supply the accepted
target/inverse bridge inputs.
-/
theorem localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtRestrEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u} :=
  localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqBridgeInputs
      inputs)

/--
The restricted-chart source-equivalence bridge inputs also supply the accepted
target/inverse bridge inputs.
-/
theorem localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u} :=
  localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
      inputs)

/--
The local forward-map agreement bridge inputs also supply the accepted
target/inverse bridge inputs.
-/
theorem localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u} :=
  localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
      inputs)

/--
The canonical transported `chartAt` inverse bridge inputs supply the accepted
local transition-model bridge inputs.
-/
theorem localForwardTransportedAtlasTransitionModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u} :=
  localForwardTransportedAtlasTransitionModelBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (localInverseTransportedAtlasModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
      inputs)

/--
The inverse-chart normal-form bridge inputs also supply the accepted local
restricted-transition bridge inputs.
-/
theorem localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardTransportedAtlasTransitionModelBridgeInputs
    (localForwardTransportedAtlasTransitionModelBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
      inputs)

/--
The canonical transported `chartAt` inverse bridge inputs also supply the
accepted local restricted-transition bridge inputs.
-/
theorem localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (localInverseTransportedAtlasModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
      inputs)

/--
The local source-equivalence bridge inputs supply the accepted local
restricted-transition bridge inputs.
-/
theorem localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartLocalForwardTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload_of_localInverseTransportedChartAtEqOnSource
      inputs.ambientChartLocalInverseTransportedChartAtEqOnSource

/--
The unfolded target/source and inverse-map bridge inputs supply the accepted
local restricted-transition bridge inputs.
-/
theorem localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
    (localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
      inputs)

/--
The local transition normal-form bridge inputs also supply the accepted
one-directional current frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardTransportedAtlasTransitionModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  forwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardChartTransportedAtlasCompatibleBridgeInputs
    (localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardTransportedAtlasTransitionModelBridgeInputs
      inputs)

/--
The inverse-chart normal-form bridge inputs also supply the accepted
one-directional current frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  forwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardChartTransportedAtlasCompatibleBridgeInputs
    (localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
      inputs)

/--
The canonical transported `chartAt` inverse bridge inputs also supply the
accepted one-directional current frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedAtlasModelBridgeInputs
    (localInverseTransportedAtlasModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
      inputs)

/--
The local source-equivalence bridge inputs also supply the accepted
one-directional current frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  forwardChartTransportedAtlasCompatibleBridgeInputs_of_localForwardChartTransportedAtlasCompatibleBridgeInputs
    (localForwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
      inputs)

/--
The unfolded target/source and inverse-map bridge inputs also supply the
accepted one-directional current frontier input.
-/
theorem forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} :=
  forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
    (localInverseTransportedChartAtEqOnSourceBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
      inputs)

/--
The one-directional bridge inputs recover the two-sided cross-atlas bridge
inputs by groupoid inversion.
-/
theorem chartTransportedAtlasCompatibleBridgeInputs_of_forwardChartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u} where
  recognize := inputs.recognize
  ambientChartTransportedAtlasCompatibility :=
    onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_forwardChartTransportedAtlasCompatibility
      inputs.ambientChartForwardTransportedAtlasCompatibility

/--
The narrower bridge-input API supplies ambient charts as members of the
transported smooth maximal atlas.
-/
theorem onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientChartInTransportedMaximalAtlasPayload.{u} :=
  onePointRecognitionAmbientChartInTransportedMaximalAtlasPayload_of_chartTransportedAtlasCompatibility
    inputs.ambientChartTransportedAtlasCompatibility

/--
The narrower bridge-input API supplies the raw ambient atlas transition
compatibility needed to build the ambient `HasGroupoid` instance.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} :=
  onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_chartTransportedAtlasCompatibility
    inputs.ambientChartTransportedAtlasCompatibility

/--
Once cross-atlas compatibility is supplied explicitly, one-point recognition
constructs the package fields through the theorem-shaped bridge without
requiring ambient atlas equality.
-/
theorem smoothabilityPackageBridgeFields_of_chartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartTransportedAtlasCompatibility
    inputs.recognize
    inputs.ambientChartTransportedAtlasCompatibility

/--
Once the forward cross-atlas transition theorem is supplied explicitly,
one-point recognition constructs the package fields through the theorem-shaped
bridge without requiring ambient atlas equality.
-/
theorem smoothabilityPackageBridgeFields_of_forwardChartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartForwardTransportedAtlasCompatibility
    inputs.recognize
    inputs.ambientChartForwardTransportedAtlasCompatibility

/--
Once the local restricted-transition source is supplied explicitly, one-point
recognition constructs the package fields through the theorem-shaped bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localForwardChartTransportedAtlasCompatibleBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibility
    inputs.recognize
    inputs.ambientChartLocalForwardTransportedAtlasCompatibility

/--
Once the local transition normal-form source is supplied explicitly, one-point
recognition constructs the package fields through the theorem-shaped bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localForwardTransportedAtlasTransitionModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModel
    inputs.recognize
    inputs.ambientChartLocalForwardTransportedAtlasTransitionModel

/--
Once the inverse-chart normal form is supplied explicitly, one-point recognition
constructs the package fields through the theorem-shaped bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localInverseTransportedAtlasModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalInverseTransportedAtlasModel
    inputs.recognize
    inputs.ambientChartLocalInverseTransportedAtlasModel

/--
Once the canonical transported `chartAt` inverse model is supplied explicitly,
one-point recognition constructs the package fields through the theorem-shaped
bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localInverseTransportedChartAtModelBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localInverseTransportedAtlasModelBridgeInputs
    (localInverseTransportedAtlasModelBridgeInputs_of_localInverseTransportedChartAtModelBridgeInputs
      inputs)

/--
Once the local source-equivalence inverse model is supplied explicitly, the
forward transported-atlas compatibility bridge constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_forwardChartTransportedAtlasCompatibleBridgeInputs
    (forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtEqOnSourceBridgeInputs
      inputs)

/--
Once the unfolded target/source and inverse-map identities are supplied
explicitly, the forward transported-atlas compatibility bridge constructs the
package fields.
-/
theorem smoothabilityPackageBridgeFields_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_forwardChartTransportedAtlasCompatibleBridgeInputs
    (forwardChartTransportedAtlasCompatibleBridgeInputs_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
      inputs)

/--
Once the manifold-side local source-intersection and forward-chart equality germ
is supplied explicitly, one-point recognition constructs the package fields
through the accepted target/inverse bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localInverseTransportedChartAtTargetEqInvEqBridgeInputs
    (localInverseTransportedChartAtTargetEqInvEqBridgeInputs_of_localTransportedChartAtSourceEqChartEqBridgeInputs
      inputs)

/--
Once the local restriction-equality chart germ is supplied explicitly, one-point
recognition constructs the package fields through the accepted manifold-side
chart-germ bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtRestrEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqBridgeInputs
      inputs)

/--
Once the restricted-chart source-equivalence germ is supplied explicitly,
one-point recognition constructs the package fields through the accepted
manifold-side chart-germ bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceEqChartEqBridgeInputs
    (localTransportedChartAtSourceEqChartEqBridgeInputs_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
      inputs)

/--
Once local forward-map agreement is supplied explicitly, one-point recognition
constructs the package fields through the restricted-chart source-equivalence
bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtRestrEqOnSourceBridgeInputs
    (localTransportedChartAtRestrEqOnSourceBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
      inputs)

/--
Once the source-restricted chart germ is supplied explicitly, one-point
recognition constructs the package fields through the local forward-map
agreement bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtChartEqOnSourceBridgeInputs
    (localTransportedChartAtChartEqOnSourceBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
      inputs)

/--
Once common-source chart-germ equality is supplied explicitly, one-point
recognition constructs the package fields through the source-germ bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceGermEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceGermEqBridgeInputs
    (localTransportedChartAtSourceGermEqBridgeInputs_of_localTransportedChartAtCommonSourceGermEqBridgeInputs
      inputs)

/--
Once model-side transition identity is supplied explicitly, one-point
recognition constructs the package fields through the common-source chart-germ
bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceGermEqBridgeInputs
    (localTransportedChartAtCommonSourceGermEqBridgeInputs_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
      inputs)

/--
Once chart-map agreement on the actual transition source is supplied explicitly,
one-point recognition constructs the package fields through the model-side
transition-identity bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
    (localTransportedChartAtCommonSourceTransitionIdBridgeInputs_of_localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs
      inputs)

/--
Once right-inverse behavior on the actual transition source is supplied
explicitly, one-point recognition constructs the package fields through the
transition-source chart-map bridge.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs
    (localTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs_of_localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs
      inputs)

/--
Once target membership and inverse equality on the actual transition source are
supplied explicitly, one-point recognition constructs the package fields through
the transition-source right-inverse bridge.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs
    (localTransportedChartAtCommonSourceTransitionRightInvBridgeInputs_of_commonSourceTransitionRightInvSplitBridgeInputs
      inputs)

/--
Once point target membership and common-target inverse source/chart facts are
supplied explicitly, one-point recognition constructs the package fields through
the transition-source split route.
-/
theorem smoothabilityPackageBridgeFields_of_pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvSplitBridgeInputs
    (commonSourceTransitionRightInvSplitBridgeInputs_of_pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs
      inputs)

/--
Once point target membership and selected-target inverse source/chart facts are
supplied explicitly, one-point recognition constructs the package fields through
the transition-source split route.
-/
theorem smoothabilityPackageBridgeFields_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvSplitBridgeInputs
    (commonSourceTransitionRightInvSplitBridgeInputs_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs
      inputs)

/--
Once pointwise chart equality and selected-target source-inclusion/chart-map
facts are supplied explicitly, one-point recognition constructs the package
fields through the selected-target point/source/chart bridge.
-/
theorem smoothabilityPackageBridgeFields_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs
    (pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
      inputs)

/--
Once pointwise chart equality and lower common-target source-inclusion/chart-map
facts are supplied explicitly, one-point recognition constructs the package
fields through the point-target/common-target bridge.
-/
theorem smoothabilityPackageBridgeFields_of_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs
    (pointTargetMemCommonTargetSymmSourceChartEqBridgeInputs_of_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
      inputs)

/--
Once target-preimage chart-map agreement and pointwise chart equality are
supplied, one-point recognition constructs the package fields through the
current point-equality/common-target bridge.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_via_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (pointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
      inputs)

/--
Once model-target transition identity is supplied explicitly, one-point
recognition constructs the package fields through the accepted transition route.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonTargetTransitionIdBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonSourceTransitionIdBridgeInputs
    (localTransportedChartAtCommonSourceTransitionIdBridgeInputs_of_localTransportedChartAtCommonTargetTransitionIdBridgeInputs
      inputs)

/--
Once explicit chart-map agreement on the transition source is supplied,
one-point recognition constructs the package fields through the accepted route.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtCommonTargetTransitionIdBridgeInputs
    (localTransportedChartAtCommonTargetTransitionIdBridgeInputs_of_localTransportedChartAtTargetPreimageChartMapEqBridgeInputs
      inputs)

/--
Once the target-preimage right-inverse source is supplied, one-point recognition
constructs the package fields through the accepted route.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageRightInvBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageChartMapEqBridgeInputs
    (localTransportedChartAtTargetPreimageChartMapEqBridgeInputs_of_localTransportedChartAtTargetPreimageRightInvBridgeInputs
      inputs)

/--
Once target membership and inverse equality on the transition source are
supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageRightInvBridgeInputs
    (localTransportedChartAtTargetPreimageRightInvBridgeInputs_of_localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs
      inputs)

/--
Once the split target-preimage sources are supplied, one-point recognition
constructs the package fields through the accepted route.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageTargetInvEqSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs
    (localTransportedChartAtTargetPreimageTargetInvEqBridgeInputs_of_targetPreimageTargetInvEqSplitBridgeInputs
      inputs)

/--
Once local target/source equivalence and common-target inverse equality are
supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetSourceIffCommonTargetInvEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageTargetInvEqSplitBridgeInputs
    (targetPreimageTargetInvEqSplitBridgeInputs_of_targetSourceIffCommonTargetInvEqBridgeInputs
      inputs)

/--
Once one-sided target membership and the common-target forward inverse source
are supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetSourceIffCommonTargetInvEqBridgeInputs
    (targetSourceIffCommonTargetInvEqBridgeInputs_of_targetMemCommonTargetSymmSourceChartEqBridgeInputs
      inputs)

/--
Once one-sided target membership and the split common-target transported
inverse facts are supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceChartEqBridgeInputs
    (targetMemCommonTargetSymmSourceChartEqBridgeInputs_of_targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs
      inputs)

/--
Once one-sided target membership and the deeper common-target source-inclusion
and chart-map facts are supplied, one-point recognition constructs the package
fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs
    (targetMemCommonTargetSymmSourceChartEqSplitBridgeInputs_of_targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs
      inputs)

/--
Once the lower chart-map and source-inclusion facts are supplied, one-point
recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs
    (targetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs_of_targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
      inputs)

/--
Once target-preimage chart-map agreement and common-target transported inverse
convergence are supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
    (targetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs
      inputs)

/--
Once target-preimage chart-map agreement and pointwise chart equality are
supplied, one-point recognition constructs the package fields.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs
    (targetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
      inputs)

/--
Once local forward-map agreement near each source point is supplied, one-point
recognition constructs the package fields through the current
target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtChartEqOnSourceBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_localTransportedChartAtChartEqOnSourceBridgeInputs
      inputs)

/--
Once conditional source-germ chart-map agreement on transported-source points
is supplied, one-point recognition constructs the package fields through the
current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_sourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_sourceChartMapEqOnTransportedSourceBridgeInputs
      inputs)

/--
Uniform one-point recognition plus conditional source-germ chart-map agreement
on transported-source points constructs the package fields through the current
target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource_via_targetPreimagePointChartEq
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_sourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimagePointChartEq
    { recognize := recognize
      ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource := payload }

/--
Once common-source chart-germ equality is supplied, one-point recognition
constructs the package fields through the conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceGermEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_sourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimagePointChartEq
    (sourceChartMapEqOnTransportedSourceBridgeInputs_of_commonSourceGermEqBridgeInputs
      inputs)

/--
Once ambient charts are known to lie in the transported atlas and transported
atlas charts satisfy the local `chartAt` source-germ theorem, one-point
recognition constructs the package fields through the conditional source-chart
map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceGermEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (localTransportedChartAtCommonSourceGermEqBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
      inputs)

/--
The two lower transported-atlas chart-germ payloads themselves are sufficient for
the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (transportedAtlasChartAtCommonSourceGermEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceGermEq :=
        transportedAtlasChartAtCommonSourceGermEq }

/--
Once ambient charts are in the transported atlas and internal transported-atlas
transition chart-map agreement is supplied, one-point recognition constructs
the package fields through the conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasGermBridgeInputs_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source and internal transition
chart-map payload are sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceTransitionChartMapEq_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (transitionChartMapEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceTransitionChartMapEq :=
        transitionChartMapEq }

/--
Once ambient charts are in the transported atlas and internal transported-atlas
transition identity is supplied, one-point recognition constructs the package
fields through the conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_of_commonSourceTransportedAtlasTransitionIdBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source and internal transition identity
payload are sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceTransitionId_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (transitionId :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceTransitionId := transitionId }

/--
The transported-atlas common-source germ bridge inputs can be routed through
the equivalent coordinate-transition identity frontier.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_transitionId
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus internal common-source
germ equality can equivalently be routed through internal transition identity.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq_via_transitionId
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (commonSourceGermEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_transitionId
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceGermEq := commonSourceGermEq }

/--
Once the split internal transported-atlas transition facts are supplied,
one-point recognition constructs the package fields through the conditional
source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTransitionIdBridgeInputs_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus internal target membership
and inverse equality are sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceTransitionTargetMem_and_invEqOnTarget_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (targetMem :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload.{u})
    (invEqOnTarget :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceTransitionTargetMem := targetMem
      transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget := invEqOnTarget }

/--
Once point target membership and selected-target inverse source/chart-map facts
are supplied, one-point recognition constructs the package fields through the
conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTransitionIdSplitBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTransitionIdSplitBridgeInputs_of_commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus point target membership,
selected-target source inclusion, and selected-target chart-map agreement are
sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtPointTargetMem_and_targetSymmSourceInclusion_and_targetSymmChartMapEqOnSource_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (pointTargetMem :
      OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload.{u})
    (sourceInclusion :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u})
    (chartMapEqOnSource :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtPointTargetMem := pointTargetMem
      transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion :=
        sourceInclusion
      transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource :=
        chartMapEqOnSource }

/--
Once pointwise chart equality and target-preimage chart-map agreement are
supplied, one-point recognition constructs the package fields through the
conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus pointwise chart equality
and target-preimage chart-map agreement are sufficient for the current
smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtPointChartEq_and_targetPreimageChartMapEqOnSource_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (pointChartEq :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u})
    (targetPreimageChartMapEqOnSource :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtPointChartEq := pointChartEq
      transportedAtlasChartAtTargetPreimageChartMapEqOnSource :=
        targetPreimageChartMapEqOnSource }

/--
Once the target-preimage right-inverse source is supplied, one-point
recognition constructs the package fields through the conditional
source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus the target-preimage
right-inverse source are sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtTargetPreimageRightInv_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (targetPreimageRightInv :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtTargetPreimageRightInv := targetPreimageRightInv }

/--
Once the source-side transported-atlas chart-map equality is supplied,
one-point recognition constructs the package fields through the
target-preimage right-inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimageRightInv
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_of_commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus source-side chart-map
choice compatibility are sufficient for the current smoothability bridge
route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtSourceChartMapEqOnTransportedSource_via_targetPreimageRightInv
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (sourceChartMapEqOnTransportedSource :
      OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimageRightInv
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtSourceChartMapEqOnTransportedSource :=
        sourceChartMapEqOnTransportedSource }

/--
Once the transported-atlas `chartAt` selector is known to choose the given
atlas chart, the current smoothability route closes through source-side
chart-map compatibility.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_via_targetPreimageRightInv
    (commonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_of_commonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus exact `chartAt` chart
choice are sufficient for the current smoothability bridge route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtChoosesAtlasChart_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (chartAtChoosesAtlasChart :
      OnePointRecognitionTransportedAtlasChartAtChoosesAtlasChartPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtChoosesAtlasChart := chartAtChoosesAtlasChart }

/--
The transported-atlas common-source germ bridge inputs also construct the
package fields by first supplying the target-preimage right-inverse source.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_targetPreimageRightInv
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_via_sourceChartMapEqOnTransportedSource
    (commonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_of_commonSourceTransportedAtlasGermBridgeInputs
      inputs)

/--
The ambient transported-atlas membership source plus internal common-source
germ equality are sufficient for the target-preimage right-inverse route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartInTransportedAtlas_and_transportedAtlasChartAtCommonSourceGermEq_via_targetPreimageRightInv
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (chartInTransportedAtlas :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u})
    (commonSourceGermEq :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransportedAtlasGermBridgeInputs_via_targetPreimageRightInv
    { recognize := recognize
      ambientChartInTransportedAtlas := chartInTransportedAtlas
      transportedAtlasChartAtCommonSourceGermEq := commonSourceGermEq }

/--
Uniform one-point recognition plus common-source chart-germ equality constructs
the package fields through the conditional source-chart-map route.
-/
theorem smoothabilityPackageBridgeFields_of_onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEq_via_sourceChartMapEqOnTransportedSource
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (payload :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceGermEqBridgeInputs_via_sourceChartMapEqOnTransportedSource
    { recognize := recognize
      ambientChartLocalTransportedChartAtCommonSourceGermEq := payload }

/--
Once source-restricted chart-germ equality is supplied, one-point recognition
constructs the package fields through the current target-preimage/point-equality
route.
-/
theorem smoothabilityPackageBridgeFields_of_localTransportedChartAtSourceGermEqBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_localTransportedChartAtSourceGermEqBridgeInputs
      inputs)

/--
Once common-source chart-germ equality is supplied, one-point recognition
constructs the package fields through the current point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceGermEqBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceGermEqBridgeInputs
      inputs)

/--
Once common-source transition identity is supplied, one-point recognition
constructs the package fields through the current point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransitionIdBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionIdBridgeInputs
      inputs)

/--
Once transition-source chart-map agreement is supplied, one-point recognition
constructs the package fields through the current target-preimage/point-equality
route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransitionChartMapEqBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionChartMapEqBridgeInputs
      inputs)

/--
Once transition-source right-inverse behavior is supplied, one-point recognition
constructs the package fields through the current target-preimage/point-equality
route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionRightInvBridgeInputs
      inputs)

/--
Once the split transition-source target-membership and inverse-equality facts
are supplied, one-point recognition constructs the package fields through the
current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvSplitBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
    (targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_of_commonSourceTransitionRightInvSplitBridgeInputs
      inputs)

/--
Once point target membership and selected-target inverse source/chart facts are
supplied, one-point recognition constructs the package fields through the
current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_commonSourceTransitionRightInvSplitBridgeInputs_via_targetPreimagePointChartEq
    (commonSourceTransitionRightInvSplitBridgeInputs_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs
      inputs)

/--
Once pointwise chart equality and selected-target source-inclusion/chart-map
facts are supplied, one-point recognition constructs the package fields through
the current target-preimage/point-equality route.
-/
theorem smoothabilityPackageBridgeFields_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_via_targetPreimagePointChartEq
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_via_targetPreimagePointChartEq
    (pointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs
      inputs)

/--
Target-preimage chart-map agreement plus pointwise chart equality supplies the
selected-target lower route through the current target-preimage/point-equality
bridge.
-/
theorem smoothabilityPackageBridgeFields_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_via_commonSourceTransitionTarget
    (inputs :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u}) :
    SmoothabilityPackageBridgeFields.{u} :=
  smoothabilityPackageBridgeFields_of_pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_via_targetPreimagePointChartEq
    (pointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_of_targetPreimageChartMapEqOnSourcePointChartEqBridgeInputs
      inputs)

/--
The narrower explicit bridge input is blocked exactly at the cross-atlas
transition compatibility between ambient charts and the transported one-point
atlas.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs_currently_blocked_at_chartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u} →
      False := by
  intro inputs
  exact compatibilityUnavailable
    inputs.ambientChartTransportedAtlasCompatibility

/--
The one-directional explicit bridge input is blocked exactly at the forward
cross-atlas transition theorem from ambient charts to transported charts.
-/
theorem onePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs_currently_blocked_at_forwardChartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibleBridgeInputs.{u} →
      False := by
  intro inputs
  exact compatibilityUnavailable
    inputs.ambientChartForwardTransportedAtlasCompatibility

/--
The local-source explicit bridge input is blocked exactly at the local
restricted-transition theorem for forward cross-atlas changes of chart.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs_currently_blocked_at_localForwardChartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasCompatibleBridgeInputs.{u} →
      False := by
  intro inputs
  exact compatibilityUnavailable
    inputs.ambientChartLocalForwardTransportedAtlasCompatibility

/--
The local transition normal-form bridge input is blocked exactly at the local
transition-model theorem.
-/
theorem onePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs_currently_blocked_at_localForwardTransportedAtlasTransitionModel
    (transitionModelUnavailable :
      OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalForwardTransportedAtlasTransitionModelBridgeInputs.{u} →
      False := by
  intro inputs
  exact transitionModelUnavailable
    inputs.ambientChartLocalForwardTransportedAtlasTransitionModel

/--
The inverse-chart bridge input is blocked exactly at the local inverse-chart
normal-form theorem.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs_currently_blocked_at_localInverseTransportedAtlasModel
    (inverseModelUnavailable :
      OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalInverseTransportedAtlasModelBridgeInputs.{u} →
      False := by
  intro inputs
  exact inverseModelUnavailable
    inputs.ambientChartLocalInverseTransportedAtlasModel

/--
The canonical transported `chartAt` inverse bridge input is blocked exactly at
the local inverse-chart theorem with the transported chart fixed to `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs_currently_blocked_at_localInverseTransportedChartAtModel
    (chartAtModelUnavailable :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtModelBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtModelUnavailable
    inputs.ambientChartLocalInverseTransportedChartAtModel

/--
The local source-equivalence bridge input is blocked exactly at the restricted
inverse-chart source-equivalence theorem.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs_currently_blocked_at_localInverseTransportedChartAtEqOnSource
    (eqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact eqOnSourceUnavailable
    inputs.ambientChartLocalInverseTransportedChartAtEqOnSource

/--
The unfolded target/source and inverse-map bridge input is blocked exactly at
that local restriction identity.
-/
theorem onePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs_currently_blocked_at_localInverseTransportedChartAtTargetEqInvEq
    (targetEqInvEqUnavailable :
      OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalInverseTransportedChartAtTargetEqInvEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetEqInvEqUnavailable
    inputs.ambientChartLocalInverseTransportedChartAtTargetEqInvEq

/--
The manifold-side local chart-germ bridge input is blocked exactly at local
source-intersection equality and forward-chart equality with the transported
`chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs_currently_blocked_at_localTransportedChartAtSourceEqChartEq
    (sourceEqChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceEqChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceEqChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtSourceEqChartEq

/--
The local restriction-equality chart-germ bridge input is blocked exactly at
equality of the restricted ambient chart and transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs_currently_blocked_at_localTransportedChartAtRestrEq
    (restrEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact restrEqUnavailable
    inputs.ambientChartLocalTransportedChartAtRestrEq

/--
The restricted-chart source-equivalence bridge input is blocked exactly at
`EqOnSource` of the restricted ambient chart and transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs_currently_blocked_at_localTransportedChartAtRestrEqOnSource
    (restrEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtRestrEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact restrEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtRestrEqOnSource

/--
The local forward-map agreement bridge input is blocked exactly at pointwise
agreement of the ambient chart and transported `chartAt` near each source point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs_currently_blocked_at_localTransportedChartAtChartEqOnSource
    (chartEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtChartEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtChartEqOnSource

/--
The source-restricted chart-germ bridge input is blocked exactly at equality
eventually in `𝓝[c.source] p` between each ambient chart and transported
`chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs_currently_blocked_at_localTransportedChartAtSourceGermEq
    (sourceGermEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceGermEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceGermEqUnavailable
    inputs.ambientChartLocalTransportedChartAtSourceGermEq

/--
The conditional source-germ bridge input is blocked exactly at chart-map
agreement on transported-source points near each ambient source point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs_currently_blocked_at_sourceChartMapEqOnTransportedSource
    (sourceChartMapEqOnTransportedSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceChartMapEqOnTransportedSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtSourceChartMapEqOnTransportedSource

/--
The common-source chart-germ bridge input is blocked exactly at equality
eventually on the common source of the ambient chart and transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs_currently_blocked_at_localTransportedChartAtCommonSourceGermEq
    (commonSourceGermEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceGermEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonSourceGermEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceGermEq

/--
The transported-atlas local chart-germ bridge input is blocked if ambient charts
cannot be placed in the transported one-point atlas.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs_currently_blocked_at_chartInTransportedAtlas
    (chartInTransportedAtlasUnavailable :
      OnePointRecognitionAmbientChartInTransportedAtlasPayload.{u} → False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartInTransportedAtlasUnavailable
    inputs.ambientChartInTransportedAtlas

/--
The transported-atlas local chart-germ bridge input is blocked if the internal
transported-atlas `chartAt` common-source germ theorem is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceGermEq
    (transportedAtlasChartAtCommonSourceGermEqUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceGermEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceGermEqUnavailable
    inputs.transportedAtlasChartAtCommonSourceGermEq

/--
Because the internal common-source germ payload implies transition identity, a
failure to prove that local coordinate-transition identity is also a failure of
the transported-atlas germ bridge input.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionId
    (transportedAtlasChartAtCommonSourceTransitionIdUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasGermBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceTransitionIdUnavailable
    (onePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload_of_commonSourceGermEq
      inputs.transportedAtlasChartAtCommonSourceGermEq)

/--
The transported-atlas transition chart-map bridge input is blocked if the
internal chart-map agreement theorem is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionChartMapEq
    (transportedAtlasChartAtCommonSourceTransitionChartMapEqUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionChartMapEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceTransitionChartMapEqUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionChartMapEq

/--
The transported-atlas transition-identity bridge input is blocked if the
internal coordinate-transition identity theorem is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionId
    (transportedAtlasChartAtCommonSourceTransitionIdUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionIdPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceTransitionIdUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionId

/--
Since internal transition identity implies the target-preimage right-inverse
source, failure of that lower right-inverse source blocks the transported-atlas
transition-identity bridge input.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs_currently_blocked_at_transportedAtlasChartAtTargetPreimageRightInv
    (targetPreimageRightInvUnavailable :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageRightInvUnavailable
    (onePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload_of_transitionId
      inputs.transportedAtlasChartAtCommonSourceTransitionId)

/--
The split transported-atlas transition-identity bridge input is blocked at
target membership on the actual internal transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionTargetMem
    (transportedAtlasChartAtCommonSourceTransitionTargetMemUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceTransitionTargetMemUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionTargetMem

/--
The split transported-atlas transition-identity bridge input is blocked at
inverse-map equality on the selected-target restriction of the internal
transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget
    (transportedAtlasChartAtCommonSourceTransitionInvEqOnTargetUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTransitionIdSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact transportedAtlasChartAtCommonSourceTransitionInvEqOnTargetUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionInvEqOnTarget

/--
The point-target/selected-target transported-atlas bridge input is blocked at
point target membership for the selected transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtPointTargetMem
    (pointTargetMemUnavailable :
      OnePointRecognitionTransportedAtlasChartAtPointTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointTargetMemUnavailable inputs.transportedAtlasChartAtPointTargetMem

/--
The point-target/selected-target transported-atlas bridge input is blocked at
selected-target transported inverse source inclusion.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion
    (sourceInclusionUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceInclusionUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionTargetSymmSourceInclusion

/--
The point-target/selected-target transported-atlas bridge input is blocked at
selected-target conditional chart-map agreement.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource
    (chartMapEqOnSourceUnavailable :
      OnePointRecognitionTransportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointTargetMemTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartMapEqOnSourceUnavailable
    inputs.transportedAtlasChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource

/--
The point-chart/target-preimage transported-atlas bridge input is blocked at
pointwise equality of the transported atlas chart and selected `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtPointChartEq
    (pointChartEqUnavailable :
      OnePointRecognitionTransportedAtlasChartAtPointChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointChartEqUnavailable inputs.transportedAtlasChartAtPointChartEq

/--
The point-chart/target-preimage transported-atlas bridge input is blocked at
target-preimage chart-map agreement for the selected transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtTargetPreimageChartMapEqOnSource
    (targetPreimageChartMapEqOnSourceUnavailable :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasPointChartEqTargetPreimageChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageChartMapEqOnSourceUnavailable
    inputs.transportedAtlasChartAtTargetPreimageChartMapEqOnSource

/--
The target-preimage right-inverse transported-atlas bridge input is blocked at
the local right-inverse identity for the selected transported `chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs_currently_blocked_at_transportedAtlasChartAtTargetPreimageRightInv
    (targetPreimageRightInvUnavailable :
      OnePointRecognitionTransportedAtlasChartAtTargetPreimageRightInvPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasTargetPreimageRightInvBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageRightInvUnavailable
    inputs.transportedAtlasChartAtTargetPreimageRightInv

/--
The source-side transported-atlas chart-map bridge input is blocked exactly at
the corresponding source-side chartAt-choice equality.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs_currently_blocked_at_transportedAtlasChartAtSourceChartMapEqOnTransportedSource
    (sourceChartMapEqOnTransportedSourceUnavailable :
      OnePointRecognitionTransportedAtlasChartAtSourceChartMapEqOnTransportedSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasSourceChartMapEqOnTransportedSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceChartMapEqOnTransportedSourceUnavailable
    inputs.transportedAtlasChartAtSourceChartMapEqOnTransportedSource

/--
The explicit chartAt-choice transported-atlas bridge input is blocked exactly
at the statement that the selected `chartAt p` is the given transported atlas
chart containing `p`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs_currently_blocked_at_transportedAtlasChartAtChoosesAtlasChart
    (chartAtChoosesAtlasChartUnavailable :
      OnePointRecognitionTransportedAtlasChartAtChoosesAtlasChartPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransportedAtlasChartAtChoosesAtlasChartBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtChoosesAtlasChartUnavailable
    inputs.transportedAtlasChartAtChoosesAtlasChart

/--
The model-side transition-identity bridge input is blocked exactly at local
identity of the coordinate change from the ambient chart to transported
`chartAt`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs_currently_blocked_at_localTransportedChartAtCommonSourceTransitionId
    (commonSourceTransitionIdUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionIdBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonSourceTransitionIdUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionId

/--
The transition-source chart-map bridge input is blocked exactly at local
agreement of the transported `chartAt` map with the ambient chart map on the
actual source of the coordinate transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs_currently_blocked_at_localTransportedChartAtCommonSourceTransitionChartMapEq
    (commonSourceTransitionChartMapEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonSourceTransitionChartMapEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionChartMapEq

/--
The transition-source right-inverse bridge input is blocked exactly at local
right-inverse behavior of transported `chartAt` on the actual source of the
coordinate transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs_currently_blocked_at_localTransportedChartAtCommonSourceTransitionRightInv
    (commonSourceTransitionRightInvUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonSourceTransitionRightInvUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionRightInv

/--
The split transition-source right-inverse bridge input is blocked at transported
target membership on the actual source of the coordinate transition.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs_currently_blocked_at_targetMem
    (targetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetMem

/--
The split transition-source right-inverse bridge input is blocked at inverse-map
equality on the transported-target restriction of the transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs_currently_blocked_at_invEqOnTarget
    (invEqOnTargetUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTargetPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionRightInvSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact invEqOnTargetUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionInvEqOnTarget

/--
The point-target/common-target bridge input is blocked at point target
membership.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_pointTargetMem
    (pointTargetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointTargetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtPointTargetMem

/--
The point-target/common-target bridge input is blocked at transported inverse
source membership on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_commonTargetSymmSource
    (commonTargetSymmSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSource

/--
The point-target/common-target bridge input is blocked at ambient chart equality
after applying the transported inverse on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_commonTargetSymmChartEq
    (commonTargetSymmChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartEq

/--
The point-target/selected-target bridge input is blocked at point target
membership.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_pointTargetMem
    (pointTargetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointTargetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtPointTargetMem

/--
The point-target/selected-target bridge input is blocked at transported inverse
source membership on the target-restricted transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_commonSourceTransitionTargetSymmSource
    (targetSymmSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetSymmSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSource

/--
The point-target/selected-target bridge input is blocked at ambient chart
equality after the transported inverse on the target-restricted transition
source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_commonSourceTransitionTargetSymmChartEq
    (targetSymmChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointTargetMemCommonSourceTransitionTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetSymmChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartEq

/--
The point-equality/selected-target lower bridge input is blocked at pointwise
chart equality.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_pointChartEq
    (pointChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
The point-equality/selected-target lower bridge input is blocked at selected
source inclusion after the transported inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonSourceTransitionTargetSymmSourceInclusion
    (targetSymmSourceInclusionUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusionPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetSymmSourceInclusionUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmSourceInclusion

/--
The point-equality/selected-target lower bridge input is blocked at selected
conditional chart-map equality after the transported inverse.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonSourceTransitionTargetSymmChartMapEqOnSource
    (targetSymmChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonSourceTransitionTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetSymmChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonSourceTransitionTargetSymmChartMapEqOnSource

/--
The point-equality/lower common-target bridge input is blocked at pointwise chart
equality.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_pointChartEq
    (pointChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
The point-equality/lower common-target bridge input is blocked at source
inclusion for the transported inverse on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonTargetSymmSourceInclusion
    (commonTargetSymmSourceInclusionUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceInclusionUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion

/--
The point-equality/lower common-target bridge input is blocked at conditional
ambient chart-map equality after the transported inverse on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonTargetSymmChartMapEqOnSource
    (commonTargetSymmChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource

/--
The model-target transition-identity bridge input is blocked exactly at local
identity of the coordinate change on the common ambient target/transition
source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs_currently_blocked_at_localTransportedChartAtCommonTargetTransitionId
    (commonTargetTransitionIdUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetTransitionIdBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetTransitionIdUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetTransitionId

/--
The explicit chart-map bridge input is blocked exactly at local agreement of
the transported `chartAt` map with the ambient chart map after `c.symm`.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs_currently_blocked_at_localTransportedChartAtTargetPreimageChartMapEq
    (targetPreimageChartMapEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageChartMapEqUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEq

/--
The target-preimage right-inverse bridge input is blocked exactly at local
right-inverse behavior of transported `chartAt` for the ambient inverse chart.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs_currently_blocked_at_localTransportedChartAtTargetPreimageRightInv
    (targetPreimageRightInvUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageRightInvBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageRightInvUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageRightInv

/--
The target-preimage inverse-map bridge input is blocked exactly at transported
target membership plus inverse-chart equality on the transition source.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs_currently_blocked_at_localTransportedChartAtTargetPreimageTargetInvEq
    (targetPreimageTargetInvEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageTargetInvEqUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetInvEq

/--
The split target-preimage bridge input is blocked if transported target
membership on the explicit transition source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs_currently_blocked_at_targetPreimageTargetMem
    (targetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem

/--
The split target-preimage bridge input is blocked if inverse equality on the
target-restricted transition source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs_currently_blocked_at_invEqOnTarget
    (invEqOnTargetUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageInvEqOnTargetPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetInvEqSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact invEqOnTargetUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageInvEqOnTarget

/--
The local target/source bridge input is blocked if target/source equivalence is
unavailable near the represented model point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs_currently_blocked_at_targetSourceIff
    (targetSourceIffUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetSourceIffPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetSourceIffUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetSourceIff

/--
The local target/source bridge input is blocked if common-target inverse
equality is unavailable near the represented model point.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs_currently_blocked_at_commonTargetInvEq
    (commonTargetInvEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetInvEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetSourceIffCommonTargetInvEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetInvEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetInvEq

/--
The one-sided target-membership bridge input is blocked if transported target
membership on the explicit transition source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_targetMem
    (targetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem

/--
The one-sided target-membership bridge input is blocked if the common-target
forward inverse source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs_currently_blocked_at_commonTargetSymmSourceChartEq
    (commonTargetSymmSourceChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceChartEq

/--
The split common-target bridge input is blocked if transported target
membership on the explicit transition source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs_currently_blocked_at_targetMem
    (targetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem

/--
The split common-target bridge input is blocked if ambient-source membership of
the transported inverse is unavailable on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs_currently_blocked_at_commonTargetSymmSource
    (commonTargetSymmSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSource

/--
The split common-target bridge input is blocked if ambient chart equality after
the transported inverse is unavailable on the common target.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs_currently_blocked_at_commonTargetSymmChartEq
    (commonTargetSymmChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceChartEqSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartEq

/--
The deeper common-target bridge input is blocked if transported target
membership on the explicit transition source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs_currently_blocked_at_targetMem
    (targetMemUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageTargetMemPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetMemUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageTargetMem

/--
The deeper common-target bridge input is blocked if the transported inverse
source-inclusion fact is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs_currently_blocked_at_commonTargetSymmSourceInclusion
    (commonTargetSymmSourceInclusionUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceInclusionUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion

/--
The deeper common-target bridge input is blocked if chart-map agreement after
the transported inverse is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs_currently_blocked_at_commonTargetSymmChartMapEq
    (commonTargetSymmChartMapEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetMemCommonTargetSymmSourceInclusionChartMapEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmChartMapEqUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEq

/--
The lower chart-map bridge input is blocked if target-preimage chart-map
agreement on transported source points is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_targetPreimageChartMapEqOnSource
    (targetPreimageChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource

/--
The lower chart-map bridge input is blocked if transported inverse source
inclusion into the ambient chart source is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonTargetSymmSourceInclusion
    (commonTargetSymmSourceInclusionUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmSourceInclusionPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmSourceInclusionUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmSourceInclusion

/--
The lower chart-map bridge input is blocked if conditional common-target
chart-map agreement after the transported inverse is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs_currently_blocked_at_commonTargetSymmChartMapEqOnSource
    (commonTargetSymmChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmSourceInclusionChartMapEqOnSourceBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmChartMapEqOnSource

/--
The tendsto bridge input is blocked if target-preimage chart-map agreement on
transported source points is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs_currently_blocked_at_targetPreimageChartMapEqOnSource
    (targetPreimageChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource

/--
The tendsto bridge input is blocked if transported inverse convergence along
the common target is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs_currently_blocked_at_commonTargetSymmTendsto
    (commonTargetSymmTendstoUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtCommonTargetSymmTendstoPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourceCommonTargetSymmTendstoBridgeInputs.{u} →
      False := by
  intro inputs
  exact commonTargetSymmTendstoUnavailable
    inputs.ambientChartLocalTransportedChartAtCommonTargetSymmTendsto

/--
The point-equality bridge input is blocked if target-preimage chart-map
agreement on transported source points is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_currently_blocked_at_targetPreimageChartMapEqOnSource
    (targetPreimageChartMapEqOnSourceUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact targetPreimageChartMapEqOnSourceUnavailable
    inputs.ambientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSource

/--
The point-equality bridge input is blocked if pointwise chart equality at the
source point is unavailable.
-/
theorem onePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs_currently_blocked_at_pointChartEq
    (pointChartEqUnavailable :
      OnePointRecognitionAmbientChartLocalTransportedChartAtPointChartEqPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartLocalTransportedChartAtTargetPreimageChartMapEqOnSourcePointChartEqBridgeInputs.{u} →
      False := by
  intro inputs
  exact pointChartEqUnavailable
    inputs.ambientChartLocalTransportedChartAtPointChartEq

/--
The two-sided explicit bridge input is already blocked at the one-directional
forward cross-atlas transition theorem it would have to supply.
-/
theorem onePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs_currently_blocked_at_forwardChartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientChartTransportedAtlasCompatibleBridgeInputs.{u} →
      False := by
  intro inputs
  exact compatibilityUnavailable
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility
      inputs.ambientChartTransportedAtlasCompatibility)

/--
The older atlas-equality bridge input is already blocked at the narrower
cross-atlas transition compatibility payload it would have to supply.
-/
theorem onePointRecognitionAmbientAtlasCompatibleBridgeInputs_currently_blocked_at_chartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u} → False := by
  intro inputs
  exact compatibilityUnavailable
    (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
      inputs)

/--
The older atlas-equality bridge input is already blocked at the one-directional
forward cross-atlas transition theorem it would have to supply.
-/
theorem onePointRecognitionAmbientAtlasCompatibleBridgeInputs_currently_blocked_at_forwardChartTransportedAtlasCompatibility
    (compatibilityUnavailable :
      OnePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u} → False := by
  intro inputs
  exact compatibilityUnavailable
    (onePointRecognitionAmbientChartForwardTransportedAtlasCompatibilityPayload_of_chartTransportedAtlasCompatibility
      (onePointRecognitionAmbientChartTransportedAtlasCompatibilityPayload_of_ambientAtlasCompatibleBridgeInputs
        inputs))

/--
The explicit one-point smoothability bridge input is blocked exactly at the
ambient atlas comparison field; recognition alone does not determine the
arbitrary ambient charted-space atlas.
-/
theorem onePointRecognitionAmbientAtlasCompatibleBridgeInputs_currently_blocked_at_ambientAtlasCompatibility
    (ambientAtlasUnavailable :
      OnePointRecognitionAmbientAtlasCompatibilityPayload.{u} → False) :
    OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u} → False := by
  intro inputs
  exact ambientAtlasUnavailable inputs.ambientAtlasCompatibility

/--
The generator-level atlas bridge input is blocked exactly at the missing fact
that every ambient chart is one of the selected charts of the transported
one-point charted-space construction.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtBridgeInputs_currently_blocked_at_ambientAtlasGeneratedByTransportedChartAt
    (generatedUnavailable :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtPayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtBridgeInputs.{u} →
      False := by
  intro inputs
  exact generatedUnavailable inputs.ambientAtlasGeneratedByTransportedChartAt

/--
The lower generator-level atlas bridge input is blocked exactly at the missing
identification of ambient charts with the local-inverse charts that generate
the transported one-point charted-space atlas.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartBridgeInputs_currently_blocked_at_ambientAtlasGeneratedByTransportedLocalInverseChart
    (generatedUnavailable :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartPayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedLocalInverseChartBridgeInputs.{u} →
      False := by
  intro inputs
  exact generatedUnavailable inputs.ambientAtlasGeneratedByTransportedLocalInverseChart

/--
The field-level local-inverse generator bridge input is blocked exactly at the
ambient atlas equality with the transported local-inverse generator range.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeBridgeInputs_currently_blocked_at_ambientAtlasEqTransportedLocalInverseChartRange
    (eqRangeUnavailable :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeBridgeInputs.{u} →
      False := by
  intro inputs
  exact eqRangeUnavailable inputs.ambientAtlasEqTransportedLocalInverseChartRange

/--
The core field-level range bridge input is blocked exactly at the atlas-field
comparison without the recognition-side hypotheses.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreBridgeInputs_currently_blocked_at_ambientAtlasEqTransportedLocalInverseChartRangeCore
    (coreUnavailable :
      OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact coreUnavailable inputs.ambientAtlasEqTransportedLocalInverseChartRangeCore

/--
The split core range bridge input is blocked if the ambient-atlas-to-range
inclusion is unavailable.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs_currently_blocked_at_ambientAtlasSubsetTransportedLocalInverseChartRangeCore
    (ambientSubsetUnavailable :
      OnePointRecognitionAmbientAtlasSubsetTransportedLocalInverseChartRangeCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact ambientSubsetUnavailable
    inputs.ambientAtlasSubsetTransportedLocalInverseChartRangeCore

/--
The split core range bridge input is blocked if the transported generated chart
range is not known to lie in the ambient atlas.
-/
theorem onePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs_currently_blocked_at_transportedLocalInverseChartRangeSubsetAmbientAtlasCore
    (rangeSubsetUnavailable :
      OnePointRecognitionTransportedLocalInverseChartRangeSubsetAmbientAtlasCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqTransportedLocalInverseChartRangeCoreSplitBridgeInputs.{u} →
      False := by
  intro inputs
  exact rangeSubsetUnavailable
    inputs.transportedLocalInverseChartRangeSubsetAmbientAtlasCore

/--
The source-conditioned local-inverse range bridge input is blocked if source
points for ambient atlas charts are unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs_currently_blocked_at_chartSourcePointCore
    (sourcePointUnavailable :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourcePointUnavailable (by
    intro M _top _charted c hc
    exact inputs.ambientAtlasChartSourcePointCore hc)

/--
The source-conditioned local-inverse range bridge input is blocked at the range
inclusion for source-nonempty ambient atlas charts.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs_currently_blocked_at_sourceNonemptySubsetTransportedLocalInverseChartRangeCore
    (sourceNonemptyRangeUnavailable :
      OnePointRecognitionAmbientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSourceNonemptySubsetTransportedLocalInverseChartRangeCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourceNonemptyRangeUnavailable (by
    intro M _top _charted e c hc hsource
    exact inputs.ambientAtlasSourceNonemptySubsetTransportedLocalInverseChartRangeCore e hc hsource)

/--
The one-sided transported-atlas core bridge input is blocked exactly at the
forward ambient-atlas inclusion into the transported atlas.
-/
theorem onePointRecognitionAmbientAtlasSubsetTransportedAtlasCoreBridgeInputs_currently_blocked_at_ambientAtlasSubsetTransportedAtlasCore
    (ambientSubsetUnavailable :
      OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSubsetTransportedAtlasCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact ambientSubsetUnavailable inputs.ambientAtlasSubsetTransportedAtlasCore

/--
The core generator bridge input is blocked exactly at the missing fact that
every ambient atlas chart is a selected transported `chartAt` chart.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCoreBridgeInputs_currently_blocked_at_ambientAtlasGeneratedByTransportedChartAtCore
    (generatedUnavailable :
      OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByTransportedChartAtCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact generatedUnavailable inputs.ambientAtlasGeneratedByTransportedChartAtCore

/--
The split core generator bridge input is blocked if the ambient atlas is not
known to be generated by the ambient selected-chart field.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs_currently_blocked_at_ambientAtlasGeneratedByAmbientChartAtCore
    (generatedUnavailable :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact generatedUnavailable inputs.ambientAtlasGeneratedByAmbientChartAtCore

/--
The split core generator bridge input is blocked if the ambient and transported
selected-chart fields are not known to agree.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtCompatibilityCore

/--
The pointwise split bridge input is blocked if the ambient atlas is not known
to be generated by the ambient selected-chart field.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_ambientAtlasGeneratedByAmbientChartAtCore
    (generatedUnavailable :
      OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact generatedUnavailable inputs.ambientAtlasGeneratedByAmbientChartAtCore

/--
The pointwise split bridge input is blocked if the selected charts are not
known to agree pointwise.
-/
theorem onePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtPointwiseCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasGeneratedByAmbientChartAtCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtPointwiseCompatibilityCore

/--
The exact atlas/range equality bridge input is blocked if that equality is not
available.
-/
theorem onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_ambientAtlasEqAmbientChartAtRangeCore
    (eqRangeUnavailable :
      OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact eqRangeUnavailable inputs.ambientAtlasEqAmbientChartAtRangeCore

/--
The exact atlas/range equality bridge input is also blocked if the pointwise
ambient/transported selected-chart comparison is unavailable.
-/
theorem onePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtPointwiseCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasEqAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtPointwiseCompatibilityCore

/--
The one-sided selected-chart range bridge input is blocked exactly at the
remaining ambient atlas inclusion into the ambient `chartAt` range.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_ambientAtlasSubsetAmbientChartAtRangeCore
    (subsetRangeUnavailable :
      OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact subsetRangeUnavailable (by
    intro M _top _charted c hc
    exact inputs.ambientAtlasSubsetAmbientChartAtRangeCore hc)

/--
The one-sided selected-chart range bridge input is also blocked if the
pointwise ambient/transported selected-chart comparison is unavailable.
-/
theorem onePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtPointwiseCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSubsetAmbientChartAtRangeCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtPointwiseCompatibilityCore

/--
The source-pointed selected-chart bridge input is blocked exactly at the
remaining local selector invariant.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_selectedByAmbientChartAtOnSourceCore
    (selectedUnavailable :
      OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectedUnavailable (by
    intro M _top _charted c hc
    exact inputs.ambientAtlasSelectedByAmbientChartAtOnSourceCore hc)

/--
The source-pointed selected-chart bridge input is also blocked if the pointwise
ambient/transported selected-chart comparison is unavailable.
-/
theorem onePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtPointwiseCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSelectedByAmbientChartAtOnSourceCoreChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtPointwiseCompatibilityCore

/--
The direct transported source-pointed selector bridge input is blocked exactly at
the transported selected-chart generator fact.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs_currently_blocked_at_selectedByTransportedChartAtOnSourceCore
    (selectedUnavailable :
      OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedChartAtOnSourceCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectedUnavailable (by
    intro M _top _charted e c hc
    exact inputs.ambientAtlasSelectedByTransportedChartAtOnSourceCore e hc)

/--
The constructor-level source-pointed local-inverse bridge input is blocked
exactly at the transported local-inverse chart generator fact.
-/
theorem onePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs_currently_blocked_at_selectedByTransportedLocalInverseChartOnSourceCore
    (selectedUnavailable :
      OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasSelectedByTransportedLocalInverseChartOnSourceCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectedUnavailable (by
    intro M _top _charted e c hc
    exact inputs.ambientAtlasSelectedByTransportedLocalInverseChartOnSourceCore e hc)

/--
The split source-pointed selector bridge input is blocked if source points for
ambient atlas charts are unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartSourcePointCore
    (sourcePointUnavailable :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourcePointUnavailable (by
    intro M _top _charted c hc
    exact inputs.ambientAtlasChartSourcePointCore hc)

/--
The split source-pointed selector bridge input is blocked if the ambient
`chartAt` selector-choice law on atlas chart sources is unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtSelectsAtlasChartOnSourceCore
    (selectsUnavailable :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectsUnavailable (by
    intro M _top _charted c hc q hq
    exact inputs.ambientChartAtSelectsAtlasChartOnSourceCore hc hq)

/--
The split source-pointed selector bridge input is also blocked if the pointwise
ambient/transported selected-chart comparison is unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtPointwiseCompatibilityCore
    (chartAtCompatibilityUnavailable :
      OnePointRecognitionAmbientChartAtPointwiseCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceChartAtPointwiseCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact chartAtCompatibilityUnavailable inputs.ambientChartAtPointwiseCompatibilityCore

/--
The selected-source compatibility bridge input is blocked if source points for
ambient atlas charts are unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs_currently_blocked_at_chartSourcePointCore
    (sourcePointUnavailable :
      OnePointRecognitionAmbientAtlasChartSourcePointCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact sourcePointUnavailable (by
    intro M _top _charted c hc
    exact inputs.ambientAtlasChartSourcePointCore hc)

/--
The selected-source compatibility bridge input is blocked if the ambient
`chartAt` selector-choice law on atlas chart sources is unavailable.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs_currently_blocked_at_chartAtSelectsAtlasChartOnSourceCore
    (selectsUnavailable :
      OnePointRecognitionAmbientChartAtSelectsAtlasChartOnSourceCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectsUnavailable (by
    intro M _top _charted c hc q hq
    exact inputs.ambientChartAtSelectsAtlasChartOnSourceCore hc hq)

/--
The selected-source compatibility bridge input is blocked exactly at the
remaining selected-source ambient/transported selector comparison.
-/
theorem onePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs_currently_blocked_at_selectedSourceCompatibilityCore
    (selectedCompatUnavailable :
      OnePointRecognitionAmbientChartAtSelectedSourceCompatibilityCorePayload.{u} →
        False) :
    OnePointRecognitionAmbientAtlasChartSourcePointSelectsOnSourceSelectedSourceCompatibilityCoreBridgeInputs.{u} →
      False := by
  intro inputs
  exact selectedCompatUnavailable (by
    intro M _top _charted e c hc q hq hselects
    exact inputs.ambientChartAtSelectedSourceCompatibilityCore e hc hq hselects)

/--
Package-field variant for the transported bridge: this is the smallest
non-ambient bridge surface currently buildable from one-point recognition.
-/
structure SmoothabilityPackageTransportedBridgeFields extends
    SmoothabilityPackageSmoothStructureDerivationFields.{u},
    SmoothabilityTransportedBridgePackageField.{u}

/--
Uniform one-point recognition constructs the package fields through the
transported-charted-space bridge, without requiring arbitrary ambient atlas
compatibility.
-/
theorem smoothabilityPackageTransportedBridgeFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageTransportedBridgeFields.{u} where
  toSmoothabilityPackageSmoothStructureDerivationFields :=
    smoothabilityPackageSmoothStructureDerivationFields_of_onePointRecognition
      recognize
  toSmoothabilityTransportedBridgePackageField :=
    smoothabilityTransportedBridgePackageField_of_onePointRecognition

/--
Package-field variant for the transported route through the next concrete
`SmoothabilityPackage` field after the bridge: the theorem-shaped `C∞`
smooth-manifold output, but carried on the transported charted-space witness.
-/
structure SmoothabilityPackageTransportedSmoothManifoldFields extends
    SmoothabilityPackageTransportedBridgeFields.{u},
    SmoothabilityTransportedSmoothManifoldPackageField.{u}

/--
Uniform one-point recognition constructs the transported package fields through
the smooth-manifold output without requiring arbitrary ambient charted-space
compatibility.
-/
theorem smoothabilityPackageTransportedSmoothManifoldFields_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    SmoothabilityPackageTransportedSmoothManifoldFields.{u} where
  toSmoothabilityPackageTransportedBridgeFields :=
    smoothabilityPackageTransportedBridgeFields_of_onePointRecognition
      recognize
  toSmoothabilityTransportedSmoothManifoldPackageField :=
    smoothabilityTransportedSmoothManifoldPackageField_of_onePointRecognition

/--
The transported smooth-manifold package field recovers the transported bridge
field by regularity lowering, so downstream transported consumers can depend on
the stronger `C∞` package surface alone.
-/
theorem smoothabilityTransportedBridgePackageField_of_transportedSmoothManifoldPackageField
    (field : SmoothabilityTransportedSmoothManifoldPackageField.{u}) :
    SmoothabilityTransportedBridgePackageField.{u} where
  transportedBridge :=
    smoothabilityTransportedBridgeStatement_of_transportedSmoothManifoldStatement
      field.transportedSmoothManifold

/--
The exact downstream surgery input needed after the transported smoothability
route has supplied the charted one-point compactification witness.
-/
def OnePointTransportedSurgeryPackageFamily : Prop :=
  ∀ (charted : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))))
    [T2Space (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    [SimplyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))]
    [CompactSpace (OnePoint (EuclideanSpace ℝ (Fin 3)))],
      letI : ChartedSpace ThreeManifoldModel
          (OnePoint (EuclideanSpace ℝ (Fin 3))) := charted
      ∀ [IsManifold ThreeManifoldModelWithCorners 1
          (OnePoint (EuclideanSpace ℝ (Fin 3)))],
        Nonempty (Σ n : ℕ∞ω,
          FiniteExtinctionSurgeryPackage n
            (OnePoint (EuclideanSpace ℝ (Fin 3))))

/--
The transported route's concrete finite-extinction output: the finite-extinction
statement is produced on the same transported charted-space witness supplied by
smoothability.
-/
def OnePointTransportedFiniteExtinctionPayload : Prop :=
  ∃ charted : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))),
    letI : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))) := charted
    FiniteExtinctionByRicciFlowWithSurgery
      (OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
The ordinary final-assembly surgery package family supplies the precise
one-point transported surgery family required by this route.
-/
theorem onePointTransportedSurgeryPackageFamily_of_surgeryPackages
    (surgeryPackages :
      ∀ (M : Type) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    OnePointTransportedSurgeryPackageFamily := by
  intro charted _t2 _simple _compact
  letI : ChartedSpace ThreeManifoldModel
      (OnePoint (EuclideanSpace ℝ (Fin 3))) := charted
  intro _smooth
  exact surgeryPackages (OnePoint (EuclideanSpace ℝ (Fin 3)))

/--
Transported smoothability plus the exact one-point surgery package family
reaches the concrete finite-extinction target for the one-point
compactification, without using the universal ambient charted-space bridge.
-/
theorem onePointTransportedFiniteExtinctionPayload_of_transportedSmoothManifoldFields
    (fields : SmoothabilityPackageTransportedSmoothManifoldFields.{0})
    (surgeryPackages : OnePointTransportedSurgeryPackageFamily) :
    OnePointTransportedFiniteExtinctionPayload := by
  let M := OnePoint (EuclideanSpace ℝ (Fin 3))
  letI : T2Space M := onePoint_threeSpace_t2Space
  letI : SimplyConnectedSpace M :=
    onePoint_threeSpace_simplyConnectedSpace_of_sourceChoiceCollapse
  letI : CompactSpace M := onePoint_threeSpace_compactSpace
  rcases fields.transportedSmoothManifold M ⟨Homeomorph.refl M⟩ with
    ⟨charted, smoothManifold⟩
  refine ⟨charted, ?_⟩
  letI : ChartedSpace ThreeManifoldModel M := charted
  letI : IsManifold ThreeManifoldModelWithCorners 1 M :=
    surgeryModel_isManifold_of_smoothManifold M smoothManifold
  rcases surgeryPackages charted with ⟨⟨_n, package⟩⟩
  exact finite_extinction_from_statement_payload_of_surgery_package package

/--
Transported smoothability plus the ordinary final-assembly surgery package
requirement reaches the concrete one-point finite-extinction target.
-/
theorem onePointTransportedFiniteExtinctionPayload_of_transportedSmoothManifoldFields_and_surgeryPackages
    (fields : SmoothabilityPackageTransportedSmoothManifoldFields.{0})
    (surgeryPackages :
      ∀ (M : Type) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M]
        [IsManifold ThreeManifoldModelWithCorners 1 M],
          Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    OnePointTransportedFiniteExtinctionPayload :=
  onePointTransportedFiniteExtinctionPayload_of_transportedSmoothManifoldFields
    fields
    (onePointTransportedSurgeryPackageFamily_of_surgeryPackages
      surgeryPackages)

/--
The stronger charted-space comparison API can instantiate the explicit
atlas-compatible bridge inputs.
-/
theorem ambientAtlasCompatibleBridgeInputs_of_chartedSpaceCompatibility
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (compat :
      OnePointRecognitionAmbientChartedSpaceCompatibilityPayload.{u}) :
    OnePointRecognitionAmbientAtlasCompatibleBridgeInputs.{u} where
  recognize := recognize
  ambientAtlasCompatibility :=
    onePointRecognitionAmbientAtlasCompatibilityPayload_of_chartedSpaceCompatibility
      compat

/--
If the ambient one-point-recognition `IsManifold` payload is unavailable, then
the theorem-shaped smoothability bridge is unavailable.
-/
theorem smoothabilityBridgeStatement_currently_blocked_at_onePointRecognitionAmbientSmoothabilityBridgePayload
    (payloadUnavailable :
      OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} → False) :
    SmoothabilityBridgeStatement.{u} → False := by
  intro bridge
  exact payloadUnavailable
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_smoothabilityBridgeStatement
      bridge)

/--
If the transported-to-ambient charted-space comparison is unavailable, then the
ambient one-point-recognition smoothability payload is unavailable.
-/
theorem onePointRecognitionAmbientSmoothabilityBridgePayload_currently_blocked_at_chartedSpaceComparison
    (comparisonUnavailable :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} → False) :
    OnePointRecognitionAmbientSmoothabilityBridgePayload.{u} → False := by
  intro payload
  exact comparisonUnavailable
    (onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientSmoothabilityBridgePayload
      payload)

/--
Therefore the theorem-shaped bridge is now blocked at the exact comparison
between transported and ambient charted-space `IsManifold` evidence.
-/
theorem smoothabilityBridgeStatement_currently_blocked_at_onePointRecognitionAmbientChartedSpaceComparison
    (comparisonUnavailable :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} → False) :
    SmoothabilityBridgeStatement.{u} → False :=
  smoothabilityBridgeStatement_currently_blocked_at_onePointRecognitionAmbientSmoothabilityBridgePayload
    (onePointRecognitionAmbientSmoothabilityBridgePayload_currently_blocked_at_chartedSpaceComparison
      comparisonUnavailable)

/--
A completed package supplies the exact transported-to-ambient `IsManifold`
transfer theorem by projecting its bridge back to the one-point ambient payload.
-/
theorem onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_smoothabilityPackage
    (package : SmoothabilityPackage.{u}) :
    OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} :=
  onePointRecognitionAmbientChartedSpaceComparisonPayload_of_ambientSmoothabilityBridgePayload
    (onePointRecognitionAmbientSmoothabilityBridgePayload_of_smoothabilityBridgeStatement
      package.bridge)

/--
A completed package supplies the lower-level ambient atlas transition
compatibility payload, since its bridge yields the ambient `IsManifold`
evidence and hence the ambient `HasGroupoid` compatibility.
-/
theorem onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_smoothabilityPackage
    (package : SmoothabilityPackage.{u}) :
    OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} := by
  intro M _top _t2 _charted _simple _compact e transported c c' hc hc'
  have ambient :
      IsManifold ThreeManifoldModelWithCorners 1 M :=
    onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_smoothabilityPackage
      package e transported
  letI : IsManifold ThreeManifoldModelWithCorners 1 M := ambient
  exact HasGroupoid.compatible hc hc'

/--
Thus the current transfer theorem is blocked at the raw ambient atlas
transition compatibility needed to build the ambient `HasGroupoid`.
-/
theorem onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_currently_blocked_at_ambientAtlasTransitionCompatibility
    (transitionUnavailable :
      OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} →
        False) :
    OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} →
      False := by
  intro transfer
  exact transitionUnavailable
    (by
      intro M _top _t2 _charted _simple _compact e transported c c' hc hc'
      have ambient : IsManifold ThreeManifoldModelWithCorners 1 M :=
        transfer e transported
      letI : IsManifold ThreeManifoldModelWithCorners 1 M := ambient
      exact HasGroupoid.compatible hc hc')

/--
Consequently, the smoothability package is now blocked at the raw ambient
atlas transition compatibility, a strictly lower-level `HasGroupoid` datum than
the full transported-to-ambient `IsManifold` transfer theorem.
-/
theorem smoothabilityPackage_currently_blocked_at_ambientAtlasTransitionCompatibility
    (transitionUnavailable :
      OnePointRecognitionAmbientAtlasTransitionCompatibilityPayload.{u} →
        False) :
    SmoothabilityPackage.{u} → False := by
  intro package
  exact transitionUnavailable
    (onePointRecognitionAmbientAtlasTransitionCompatibilityPayload_of_smoothabilityPackage
      package)

/--
Thus the current package blocker is precisely the missing theorem transferring
`IsManifold` from the transported one-point charted space to the ambient
charted-space instance.
-/
theorem smoothabilityPackage_currently_blocked_at_transportedToAmbientIsManifoldTransfer
    (transferUnavailable :
      OnePointRecognitionTransportedToAmbientIsManifoldTransferTheorem.{u} →
        False) :
    SmoothabilityPackage.{u} → False := by
  intro package
  exact transferUnavailable
    (onePointRecognitionTransportedToAmbientIsManifoldTransferTheorem_of_smoothabilityPackage
      package)

/--
Consequently, after smooth-structure derivation is closed, the package remains
blocked exactly at the comparison from the transported one-point charted-space
manifold evidence to the ambient charted-space instance.
-/
theorem smoothabilityPackage_currently_blocked_at_onePointRecognitionAmbientChartedSpaceComparison
    (comparisonUnavailable :
      OnePointRecognitionAmbientChartedSpaceComparisonPayload.{u} → False) :
    SmoothabilityPackage.{u} → False := by
  intro package
  exact
    smoothabilityBridgeStatement_currently_blocked_at_onePointRecognitionAmbientChartedSpaceComparison
      comparisonUnavailable package.bridge

end Poincare
