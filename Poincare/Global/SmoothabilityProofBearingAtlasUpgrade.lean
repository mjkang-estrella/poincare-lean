import Poincare.Global.SmoothabilityExistenceBridge
import Poincare.ProofProgress.MoiseSmoothabilityAfterTopologyExtraction

/-!
# C-infinity atlases from proof-bearing smoothability data

The repository's Moise and PL-smoothing records do not themselves contain a
charted-space witness or transition maps.  Their proof-bearing field is a
homeomorphism to the one-point compactification model, together with
equalities saying that the remaining records were generated from that same
recognition proof.

That recognition field is nevertheless strong enough to construct a genuine
smooth atlas: transport the concrete smooth compactification atlas along the
stored homeomorphism.  This file exposes that construction as an actual
existential `ChartedSpace`/`IsManifold` pair, derives the pointwise and
universal `C1ToCInfinityAtlasUpgrade3` interfaces from it, and connects the
result to the existing finite-extinction/topology-extraction route.

No theorem below claims that `MoiseSmoothabilityStatement` by itself supplies
the upgrade.  Its output is only a selected `C1` atlas.  The independent
generic construction of a smooth atlas from that datum remains the genuine
missing smoothing theorem; the results here apply when an existing
proof-bearing record additionally supplies one-point recognition.

The first section below also records the honest noncircular boundary.  A
local smoothing construction need only select a charted atlas and prove the
`C∞` transition-map condition used by mathlib's
`isManifold_of_contDiffOn`; coverage and local-homeomorphism data are already
part of `ChartedSpace`.  This prunes the nominal PL compatibility,
maximality, and uniqueness records, none of which currently contain atlas
data.  No recognition theorem is used in that section.
-/

noncomputable section

open scoped Manifold ContDiff

universe u

namespace Poincare

local notation "I" => closedSmoothModelWithCorners 3

/-!
## Noncircular local transition-smoothing boundary
-/

/-- The smallest proof-bearing output of a local atlas-smoothing
construction needed by mathlib's manifold API.

`smoothAtlas` contains the local homeomorphisms and their coverage.  The sole
mathematical proof field says that every transition between its atlas charts
is `C∞` in the standard three-dimensional model.  The larger nominal Moise
and PL-smoothing records are not prerequisites for this package because their
current fields are recognition equalities rather than local smoothing data.
-/
structure CInfinityLocalTransitionAtlasData3
    (M : Type u) [TopologicalSpace M] where
  smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M
  transitionContDiffOn :
    letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
    ∀ e e' : OpenPartialHomeomorph M (ClosedSmoothModel 3),
      e ∈ atlas (ClosedSmoothModel 3) M →
      e' ∈ atlas (ClosedSmoothModel 3) M →
        ContDiffOn ℝ ∞
          (I ∘ e.symm ≫ₕ e' ∘ (closedSmoothModelWithCorners 3).symm)
          ((closedSmoothModelWithCorners 3).symm ⁻¹'
            (e.symm ≫ₕ e').source ∩ Set.range I)

/-- An already constructed smooth atlas supplies the proof-bearing local
transition package directly.  The transition field is extracted from the
maximal-atlas compatibility carried by `IsManifold`; no recognition theorem
or nominal PL record is involved. -/
noncomputable def cInfinityLocalTransitionAtlasData3_of_smoothAtlas
    {M : Type u} [TopologicalSpace M]
    (smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M)
    (smoothManifold :
      letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
      IsManifold I ∞ M) :
    CInfinityLocalTransitionAtlasData3 M := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
  letI : IsManifold I ∞ M := smoothManifold
  refine ⟨smoothAtlas, ?_⟩
  intro e e' he he'
  exact
    (IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he')).1

/-- A selected atlas with proof-bearing `C∞` transition maps is exactly the
existence of a selected closed-smooth atlas carrying the corresponding
`IsManifold` proof.

The forward implication uses only `isManifold_of_contDiffOn`; the reverse
implication extracts transition compatibility from the supplied manifold
structure.  In particular, neither direction uses a recognition theorem. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas
    {M : Type u} [TopologicalSpace M] :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) ↔
      ∃ smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M,
        letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
        IsManifold I ∞ M := by
  constructor
  · rintro ⟨data⟩
    refine ⟨data.smoothAtlas, ?_⟩
    letI : ChartedSpace (ClosedSmoothModel 3) M := data.smoothAtlas
    exact isManifold_of_contDiffOn I ∞ M data.transitionContDiffOn
  · rintro ⟨smoothAtlas, smoothManifold⟩
    exact
      ⟨cInfinityLocalTransitionAtlasData3_of_smoothAtlas
        smoothAtlas smoothManifold⟩

/-- Pointwise local smoothing of a selected surgery-model `C¹` atlas.

The input `C¹` evidence is retained because it is the actual hypothesis of
the smoothing problem.  The output is strictly below
`C1ToCInfinityAtlasUpgrade3`: it gives local transition smoothness, from
which the `IsManifold` proof is constructed by the library theorem rather
than stored as another field.
-/
def C1AtlasLocalTransitionSmoothing3
    (M : Type u) [TopologicalSpace M] :=
  ∀ c1Atlas : ChartedSpace ThreeManifoldModel M,
    letI : ChartedSpace ThreeManifoldModel M := c1Atlas
    IsManifold ThreeManifoldModelWithCorners 1 M →
      CInfinityLocalTransitionAtlasData3 M

/-- A selected surgery-model `C¹` atlas together with a local transition
smoothing construction supplies one selected proof-bearing `C∞` atlas.

This is the direct fixed-target bridge between the two honest smoothability
interfaces.  It merely specializes the local construction at the atlas
selected by `AdmitsSurgeryModelSmoothStructure`; no recognition theorem is
used. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing
    {M : Type u} [TopologicalSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact ⟨localSmoothing c1Atlas c1Manifold⟩

/-- Existence of some smooth atlas is enough for the local-smoothing
interface as currently stated: its output atlas is allowed to differ from
the selected `C¹` atlas.  This equivalence-facing direction makes the true
remaining datum explicit without importing any one-point recognition. -/
noncomputable def c1AtlasLocalTransitionSmoothing3_of_exists_smoothAtlas
    {M : Type u} [TopologicalSpace M]
    (hexists :
      ∃ smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M,
        letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
        IsManifold I ∞ M) :
    C1AtlasLocalTransitionSmoothing3 M := by
  intro _c1Atlas _c1Manifold
  let smoothAtlas := Classical.choose hexists
  have smoothManifold := Classical.choose_spec hexists
  exact
    cInfinityLocalTransitionAtlasData3_of_smoothAtlas
      smoothAtlas smoothManifold

/-- Local transition smoothing constructs the exact pointwise
`C¹`-to-`C∞` atlas upgrade.  This proof uses only
`isManifold_of_contDiffOn`; it does not use one-point or sphere recognition.
-/
theorem c1ToCInfinityAtlasUpgrade3_of_localTransitionSmoothing
    {M : Type u} [TopologicalSpace M]
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M) :
    C1ToCInfinityAtlasUpgrade3 M := by
  intro c1Atlas
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  intro c1Manifold
  let data := localSmoothing c1Atlas c1Manifold
  refine ⟨data.smoothAtlas, ?_⟩
  letI : ChartedSpace (ClosedSmoothModel 3) M := data.smoothAtlas
  exact isManifold_of_contDiffOn I ∞ M data.transitionContDiffOn

/-- Conversely, a pointwise atlas upgrade contains enough data to recover
the local-transition package: select its smooth atlas and extract transition
regularity from the resulting `IsManifold` instance. -/
noncomputable def c1AtlasLocalTransitionSmoothing3_of_c1ToCInfinityAtlasUpgrade3
    {M : Type u} [TopologicalSpace M]
    (upgrade : C1ToCInfinityAtlasUpgrade3 M) :
    C1AtlasLocalTransitionSmoothing3 M := by
  intro c1Atlas
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  intro c1Manifold
  have hexists := upgrade c1Atlas c1Manifold
  let smoothAtlas := Classical.choose hexists
  have smoothManifold := Classical.choose_spec hexists
  exact
    cInfinityLocalTransitionAtlasData3_of_smoothAtlas
      smoothAtlas smoothManifold

/-- The local-transition boundary and the pointwise atlas-upgrade boundary
are propositionally equivalent.  The former is a more proof-oriented API,
but it does not hide a weaker mathematical assumption. -/
theorem nonempty_c1AtlasLocalTransitionSmoothing3_iff_c1ToCInfinityAtlasUpgrade3
    {M : Type u} [TopologicalSpace M] :
    Nonempty (C1AtlasLocalTransitionSmoothing3 M) ↔
      C1ToCInfinityAtlasUpgrade3 M :=
  ⟨fun localSmoothing ↦
      c1ToCInfinityAtlasUpgrade3_of_localTransitionSmoothing
        localSmoothing.some,
    fun upgrade ↦
      ⟨c1AtlasLocalTransitionSmoothing3_of_c1ToCInfinityAtlasUpgrade3
        upgrade⟩⟩

/-!
## Direct elimination of one selected smooth-transition atlas
-/

/-- A single selected atlas with proof-bearing `C∞` transitions installs all
instances required by the smooth normalized-flow target.

Unlike `C1AtlasLocalTransitionSmoothing3`, this constructor does not quantify
over every possible `C¹` atlas, and unlike
`AdmitsSurgeryModelSmoothStructure`, it does not require a separate `C¹`
witness.  Its only geometric step is the library theorem
`isManifold_of_contDiffOn`; second countability and connectedness follow from
compactness and simple connectivity. -/
noncomputable def smoothNormalizedFlowTargetInstances3_of_cInfinityLocalTransitionAtlasData3
    {M : Type u} [TopologicalSpace M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (data : CInfinityLocalTransitionAtlasData3 M) :
    SmoothNormalizedFlowTargetInstances3 M := by
  letI : ChartedSpace (ClosedSmoothModel 3) M := data.smoothAtlas
  let smoothManifold :
      IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    isManifold_of_contDiffOn
      (closedSmoothModelWithCorners 3) ∞ M
      data.transitionContDiffOn
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M :=
    smoothManifold
  let secondCountable : SecondCountableTopology M :=
    secondCountableTopology_for_normalizedFlow_of_compact_chartedSpace M
  let connected : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  exact
    { chartedSpace := data.smoothAtlas
      smoothManifold := smoothManifold
      secondCountableTopology := secondCountable
      connectedSpace := connected }

/-- Eliminate one selected proof-bearing smooth-transition atlas into any
conclusion uniform in the resulting normalized-flow instances.

This is the exact noncircular fixed-target smoothability boundary: it neither
uses nor produces one-point/sphere recognition. -/
theorem normalizedFlowTarget_elim_of_cInfinityLocalTransitionAtlasData3
    {M : Type u} [TopologicalSpace M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (data : CInfinityLocalTransitionAtlasData3 M)
    {P : Prop}
    (h : ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M], P) :
    P :=
  (smoothNormalizedFlowTargetInstances3_of_cInfinityLocalTransitionAtlasData3
    data).elim h

/-- A one-point recognition homeomorphism constructs an actual transported
three-dimensional `C∞` atlas and its manifold proof. -/
theorem exists_cInfinityAtlas_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    (recognized :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
      IsManifold (𝓡 3) ∞ M := by
  rcases recognized with ⟨e⟩
  let smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
    homeomorphToOnePoint_threeSpace_smoothChartedSpace e
  refine ⟨smoothAtlas, ?_⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
  exact homeomorphToOnePoint_threeSpace_smoothManifold e

/-- One-point recognition supplies the pointwise atlas upgrade independently
of the selected `C¹` atlas: the output is the transported compactification
smooth atlas. -/
theorem c1ToCInfinityAtlasUpgrade3_of_onePointRecognition
    {M : Type u} [TopologicalSpace M]
    (recognized :
      Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))) :
    C1ToCInfinityAtlasUpgrade3 M := by
  intro c1Atlas
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  intro _c1Manifold
  exact exists_cInfinityAtlas_of_onePointRecognition recognized

/-- The earliest PL-smoothing-existence record already exposes enough
recognition data to construct a genuine `C∞` atlas.  No nominal
`plSmoothingExistence` field is treated as an opaque atlas constructor. -/
theorem exists_cInfinityAtlas_of_hasPLSmoothingExistence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (smoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas) :
    ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
      IsManifold (𝓡 3) ∞ M :=
  exists_cInfinityAtlas_of_onePointRecognition
    smoothingExistence.onePointRecognition

/-- The proof-bearing PL smoothing-existence record closes the pointwise
atlas-upgrade interface through that transported witness. -/
theorem c1ToCInfinityAtlasUpgrade3_of_hasPLSmoothingExistence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (smoothingExistence :
      HasPLSmoothingExistence M triangulation plStructure plAtlas) :
    C1ToCInfinityAtlasUpgrade3 M :=
  c1ToCInfinityAtlasUpgrade3_of_onePointRecognition
    smoothingExistence.onePointRecognition

/-- The proof-bearing PL smoothing theorem produces an actual transported
`C∞` atlas through its recognition field. -/
theorem exists_cInfinityAtlas_of_hasPLSmoothingTheorem
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas) :
    ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
      IsManifold (𝓡 3) ∞ M :=
  exists_cInfinityAtlas_of_onePointRecognition
    smoothingTheorem.onePointRecognition

/-- Even the record named `HasSmoothAtlasConstruction` carries no atlas as a
field.  Its recognition field, however, constructs the transported atlas
explicitly. -/
theorem exists_cInfinityAtlas_of_hasSmoothAtlasConstruction
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    {smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas}
    {smoothStructure : HasThreeManifoldSmoothStructure M}
    (atlasConstruction :
      HasSmoothAtlasConstruction M triangulation plStructure plAtlas
        smoothingTheorem smoothStructure) :
    ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
      IsManifold (𝓡 3) ∞ M :=
  exists_cInfinityAtlas_of_onePointRecognition
    atlasConstruction.onePointRecognition

/-- A proof-bearing PL smoothing theorem closes the pointwise atlas-upgrade
interface. -/
theorem c1ToCInfinityAtlasUpgrade3_of_hasPLSmoothingTheorem
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    {triangulation : HasMoiseTriangulation M}
    {plStructure : HasCompatiblePLStructure M triangulation}
    {plAtlas : HasCompatiblePLAtlas M triangulation plStructure}
    (smoothingTheorem :
      HasPLSmoothingTheorem M triangulation plStructure plAtlas) :
    C1ToCInfinityAtlasUpgrade3 M :=
  c1ToCInfinityAtlasUpgrade3_of_onePointRecognition
    smoothingTheorem.onePointRecognition

/-- Universal one-point recognition constructs the corrected
existence-shaped smooth-manifold statement by selecting the transported atlas
on each target. -/
theorem existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _top _t2 _ambient _simple _compact
  exact exists_cInfinityAtlas_of_onePointRecognition (recognize M)

/-- Universal one-point recognition also constructs the universal pointwise
`C¹`-to-`C∞` upgrade interface. -/
theorem universalC1ToCInfinityAtlasUpgrade3_of_onePointRecognition
    (recognize : OnePointThreeSpaceRecognitionStatement.{u}) :
    UniversalC1ToCInfinityAtlasUpgrade3.{u} := by
  intro M _top _t2 _ambient _simple _compact
  exact c1ToCInfinityAtlasUpgrade3_of_onePointRecognition (recognize M)

/-- A completed smoothability package yields existence-shaped `C∞`
smoothability from its earliest proof-bearing PL smoothing-existence field.
This proof does not use the package's already-packaged `smoothManifold`
field. -/
theorem existsSmoothabilitySmoothManifoldStatement_of_smoothabilityPackage_plSmoothingExistence
    (package : SmoothabilityPackage.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _top _t2 _ambient _simple _compact
  exact exists_cInfinityAtlas_of_hasPLSmoothingExistence
    (package.plSmoothingExistence M)

/-- The same PL-smoothing-existence package field constructs the universal atlas
upgrade, without appealing to `SmoothabilityPackage.smoothManifold`. -/
theorem universalC1ToCInfinityAtlasUpgrade3_of_smoothabilityPackage_plSmoothingExistence
    (package : SmoothabilityPackage.{u}) :
    UniversalC1ToCInfinityAtlasUpgrade3.{u} := by
  intro M _top _t2 _ambient _simple _compact
  exact c1ToCInfinityAtlasUpgrade3_of_hasPLSmoothingExistence
    (package.plSmoothingExistence M)

/-- Universal finite extinction and the proof-bearing topology package
construct an actual `C∞` atlas on every target, bypassing any opaque
atlas-upgrade premise. -/
theorem existsSmoothabilitySmoothManifoldStatement_of_universalFiniteExtinction_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} :=
  existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition
    (onePointThreeSpaceRecognitionStatement_of_finite_extinction_and_topology_package
      finiteExtinction package)

/-- The same finite-extinction/topology-extraction chain constructs the
universal `C¹`-to-`C∞` upgrade interface.  The construction ignores the input
`C¹` atlas only because topology extraction already supplies a recognition
homeomorphism from which a smooth atlas can be transported. -/
theorem universalC1ToCInfinityAtlasUpgrade3_of_universalFiniteExtinction_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    UniversalC1ToCInfinityAtlasUpgrade3.{u} :=
  universalC1ToCInfinityAtlasUpgrade3_of_onePointRecognition
    (onePointThreeSpaceRecognitionStatement_of_finite_extinction_and_topology_package
      finiteExtinction package)

/-- The topology-extraction route simultaneously supplies the corrected Moise
statement and a constructed universal atlas upgrade.  The second component is
not inferred from the first; both are independently obtained from the common
recognition theorem. -/
theorem moiseSmoothability_and_universalC1ToCInfinityAtlasUpgrade3_of_universalFiniteExtinction_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    MoiseSmoothabilityStatement.{u} ∧
      UniversalC1ToCInfinityAtlasUpgrade3.{u} :=
  ⟨moiseSmoothabilityStatement_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package,
    universalC1ToCInfinityAtlasUpgrade3_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package⟩

/-- Consequently the existing Moise-plus-upgrade composition can be closed by
the proof-bearing finite-extinction/topology-extraction chain, with no opaque
upgrade argument supplied by the caller. -/
theorem existsSmoothabilitySmoothManifoldStatement_via_moiseUpgrade_of_universalFiniteExtinction_and_topologyPackage
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} :=
  existsSmoothabilitySmoothManifoldStatement_of_moiseSmoothability_and_upgrade
    (moiseSmoothabilityStatement_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package)
    (universalC1ToCInfinityAtlasUpgrade3_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package)

end Poincare
