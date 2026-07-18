import Poincare.ProofProgress.MoiseSmoothabilityTarget
import Poincare.Global.TopologicalCompletionBridge

/-!
# Existence-shaped smoothability boundary

`MoiseSmoothabilityStatement` selects a charted-space instance on which a
topological three-manifold is a `C¹` manifold.  The global Ricci-flow theorem
instead consumes a possibly different charted-space instance carrying a
`C∞` manifold structure.  This file records the exact atlas-upgrade theorem
needed between those two interfaces.

The upgrade below is deliberately a hypothesis.  The local mathlib manifold
API can lower an existing regularity level, but it does not construct a smooth
atlas from a `C¹` atlas.  Proving this upgrade is the genuine manifold-smoothing
input; the theorems after it are only quantifier-preserving composition.
-/

noncomputable section

open scoped Manifold ContDiff

universe u

namespace Poincare

/--
Pointwise three-dimensional atlas upgrade from a selected `C¹` atlas to some
`C∞` atlas on the same topological space.

The output atlas need not be the input atlas or any ambient atlas already in
scope.  Both manifold propositions are therefore kept underneath the `letI`
that selects the charted-space instance on which they are asserted.
-/
def C1ToCInfinityAtlasUpgrade3
    (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ c1Atlas : ChartedSpace ThreeManifoldModel M,
    letI : ChartedSpace ThreeManifoldModel M := c1Atlas
    IsManifold ThreeManifoldModelWithCorners 1 M →
      ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
        IsManifold (𝓡 3) ∞ M

/-- The pointwise atlas-upgrade interface exposes its dependent quantifiers. -/
theorem c1ToCInfinityAtlasUpgrade3_eq
    (M : Type u) [TopologicalSpace M] :
    C1ToCInfinityAtlasUpgrade3 M =
      (∀ c1Atlas : ChartedSpace ThreeManifoldModel M,
        letI : ChartedSpace ThreeManifoldModel M := c1Atlas
        IsManifold ThreeManifoldModelWithCorners 1 M →
          ∃ smoothAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
            letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := smoothAtlas
            IsManifold (𝓡 3) ∞ M) :=
  rfl

/--
Universal atlas-upgrade hypothesis on the compact simply connected
three-manifolds quantified by the project statement.

This proposition names the genuine missing smoothing theorem.  It is not
constructed in this module.
-/
def UniversalC1ToCInfinityAtlasUpgrade3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      C1ToCInfinityAtlasUpgrade3 M

/-- The universal atlas-upgrade interface exposes its target-manifold scope. -/
theorem universalC1ToCInfinityAtlasUpgrade3_eq :
    UniversalC1ToCInfinityAtlasUpgrade3.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace ThreeManifoldModel M]
        [SimplyConnectedSpace M] [CompactSpace M],
          C1ToCInfinityAtlasUpgrade3 M) :=
  rfl

/-!
## Fixed-target normalized-flow instance bridge

The normalized-flow sphere endpoint is stated for a closed smooth
three-manifold.  At a fixed target, compactness and simple connectivity
already supply two of its instance hypotheses after a smooth atlas has been
selected:

* compactness makes the charted space sigma compact, hence second countable;
* simple connectivity supplies connectedness.

The surgery and closed-smooth model spaces are definitionally the same
Euclidean three-space.  The only nonformal step is therefore the atlas
regularity upgrade recorded by `C1ToCInfinityAtlasUpgrade3 M`.
-/

/-- A compact charted three-manifold over the closed-smooth model is second
countable.  This is the exact topology instance used by the normalized-flow
endpoint after its smooth atlas has been selected. -/
theorem secondCountableTopology_for_normalizedFlow_of_compact_chartedSpace
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M] [CompactSpace M] :
    SecondCountableTopology M :=
  ChartedSpace.secondCountable_of_sigmaCompact
    (H := ClosedSmoothModel 3) M

/-- A simply connected target is connected, as required by the
normalized-flow endpoint. -/
theorem connectedSpace_for_normalizedFlow_of_simplyConnectedSpace
    (M : Type u) [TopologicalSpace M] [SimplyConnectedSpace M] :
    ConnectedSpace M :=
  inferInstance

/-- `AdmitsSurgeryModelSmoothStructure` supplies a selected `C¹` atlas.
The single genuine smoothing input upgrades that selected atlas to some
possibly different `C∞` atlas.  The surgery and closed-smooth model names
need no additional transport theorem because both reduce to Euclidean
three-space and its standard model with corners. -/
theorem exists_closedSmooth_cInfinityAtlas_of_admitsSurgeryModelSmoothStructure
    {M : Type u} [TopologicalSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (upgrade : C1ToCInfinityAtlasUpgrade3 M) :
    ∃ smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M,
      letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
      IsManifold (closedSmoothModelWithCorners 3) ∞ M := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  exact upgrade c1Atlas c1Manifold

/-- The four instance witnesses needed to move from a target-layer compact,
simply connected topological three-manifold to the smooth normalized-flow
interface.

The package is data-valued because it retains a selected atlas.  It is
eliminated inside a proof, where that atlas and the accompanying typeclass
witnesses can be installed locally.  No recognition homeomorphism is present
in the data. -/
structure SmoothNormalizedFlowTargetInstances3
    (M : Type u) [TopologicalSpace M] where
  chartedSpace : ChartedSpace (ClosedSmoothModel 3) M
  smoothManifold :
    letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
    IsManifold (closedSmoothModelWithCorners 3) ∞ M
  secondCountableTopology : SecondCountableTopology M
  connectedSpace : ConnectedSpace M

/-- The noncircular fixed-target bridge.  Every field except the `C¹`-to-`C∞`
atlas step is constructed from the target's existing compactness and simple
connectivity instances. -/
noncomputable def smoothNormalizedFlowTargetInstances3_of_admitsSurgeryModelSmoothStructure
    {M : Type u} [TopologicalSpace M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (upgrade : C1ToCInfinityAtlasUpgrade3 M) :
    SmoothNormalizedFlowTargetInstances3 M := by
  classical
  let hExists :=
    exists_closedSmooth_cInfinityAtlas_of_admitsSurgeryModelSmoothStructure
      admits upgrade
  let smoothAtlas : ChartedSpace (ClosedSmoothModel 3) M :=
    Classical.choose hExists
  letI : ChartedSpace (ClosedSmoothModel 3) M := smoothAtlas
  have smoothManifold :
      IsManifold (closedSmoothModelWithCorners 3) ∞ M := by
    simpa only [smoothAtlas, hExists] using Classical.choose_spec hExists
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M := smoothManifold
  let secondCountable : SecondCountableTopology M :=
    secondCountableTopology_for_normalizedFlow_of_compact_chartedSpace M
  let connected : ConnectedSpace M :=
    connectedSpace_for_normalizedFlow_of_simplyConnectedSpace M
  exact
    { chartedSpace := smoothAtlas
      smoothManifold := smoothManifold
      secondCountableTopology := secondCountable
      connectedSpace := connected }

/-- Install the selected smooth atlas and all derived normalized-flow target
instances while proving an instance-independent conclusion.  This is the
direct application bridge for universal smooth normalized-flow conclusions,
including the sphere endpoint. -/
theorem SmoothNormalizedFlowTargetInstances3.elim
    {M : Type u} [TopologicalSpace M]
    (instances : SmoothNormalizedFlowTargetInstances3 M)
    {P : Prop}
    (h : ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M], P) :
    P := by
  rcases instances with
    ⟨chartedSpace, smoothManifold, secondCountable, connected⟩
  letI : ChartedSpace (ClosedSmoothModel 3) M := chartedSpace
  letI : IsManifold (closedSmoothModelWithCorners 3) ∞ M := smoothManifold
  letI : SecondCountableTopology M := secondCountable
  letI : ConnectedSpace M := connected
  exact h

/-- One-step eliminator from the corrected Moise-shaped pointwise premise to
any conclusion available uniformly on smooth normalized-flow targets.  The
only extra geometric premise is `C1ToCInfinityAtlasUpgrade3 M`; no
one-point or sphere recognition route is used. -/
theorem normalizedFlowTarget_elim_of_admitsSurgeryModelSmoothStructure
    {M : Type u} [TopologicalSpace M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (upgrade : C1ToCInfinityAtlasUpgrade3 M)
    {P : Prop}
    (h : ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M], P) :
    P :=
  (smoothNormalizedFlowTargetInstances3_of_admitsSurgeryModelSmoothStructure
    admits upgrade).elim h

/--
Moise's existence-shaped `C¹` statement and the genuine atlas-upgrade theorem
produce the existence-shaped `C∞` smoothability input used by topological
completion.
-/
theorem existsSmoothabilitySmoothManifoldStatement_of_moiseSmoothability_and_upgrade
    (moise : MoiseSmoothabilityStatement.{u})
    (upgrade : UniversalC1ToCInfinityAtlasUpgrade3.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _top _t2 _ambient _simplyConnected _compact
  rcases moise M with ⟨c1Atlas, hc1⟩
  exact upgrade M c1Atlas hc1

/--
Honest smoothability-to-Poincare boundary: Moise `C¹` existence, the explicit
`C¹`-to-`C∞` atlas upgrade, reduced Hamilton convergence, and compatible
Cartan germs imply the canonical topological Poincare statement.

Only the composition is proved here.  In particular, the atlas-upgrade
hypothesis remains visible and is not replaced by ambient-atlas compatibility.
-/
theorem poincareConjectureStatement_of_moiseSmoothability_of_upgrade_of_hamiltonConvergenceCore_of_compatibleCartanAtlas
    (moise : MoiseSmoothabilityStatement.{u})
    (upgrade : UniversalC1ToCInfinityAtlasUpgrade3.{u})
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_of_hamiltonConvergenceCore_of_compatibleCartanAtlas
    (existsSmoothabilitySmoothManifoldStatement_of_moiseSmoothability_and_upgrade
      moise upgrade)
    hHamilton hAtlas

end Poincare
