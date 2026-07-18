import Poincare.Global.NormalizedFlowQuantitativeNearRoundTailFromDecay
import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary
import Poincare.Global.SmoothabilityPLCompatibleAffineConjugacy

/-!
# End-to-end finite-smoothing and reaction-decay boundary

This file combines the strongest current noncircular reductions without
silently assuming that a smooth atlas has already been selected.

On a compact topological three-manifold, compactness first produces a finite
precompact atlas and its finite nerve.  A PL-compatible affine-conjugacy solver
supplies one coordinate correction per vertex and pointwise locally invertible
affine transition models.  Compactness extracts a finite patch family, whose
restricted affine equivalences construct an actual `C∞` atlas.
Only after that atlas is installed do the fixed-target normalized-flow and
Cartan providers run.  The analytic provider starts from uniform relative
traceless-Ricci decay and scalar-to-mean oscillation decay, synchronizes a
finite tail, and derives the Ricci floor `3R/10`, positive scalar curvature,
and scalar-to-mean factor `3/2`.  The Hamilton coefficient gap, exact reaction
evolution, Ricci quotient bound, and tail decay rate are then derived, while
continuity handles the initial interval.
The Cartan provider exposes moving fixed-chart source data and finite
post-realization adaptive grid coherence used by the direct recognition
theorem; the generic successor cover is constructed internally.

Consequently, the structure below stores neither an `IsManifold` proof nor a
sphere-recognition conclusion.  Its remaining inputs are precisely the
finite smoothing solver and the geometric forward analytic/Cartan data.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalFamilyComparedNeighborhood
open CartanCanonicalFamilyComparedForwardNormalRegularity
open CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope
open CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
open CartanSourceExponential
open CartanTargetExponential
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open SmoothabilityPLCompatibleAffineConjugacy

/-- Fixed-target quantitative near-round-from-decay analytic data.  The
quantification over smooth instances lets the data be requested only after
the finite smoothing solver has constructed the selected atlas. -/
def FixedTargetNormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3.{u, v}
        M

/-- The strongest current end-to-end fixed-manifold boundary.

The first fields are one compactness-selected finite nerve reduction and the
pointwise PL-compatible affine-conjugacy package on it.  The remaining fields
are requested uniformly after the derived local diffeomorphisms install their
smooth atlas.  No smooth atlas, manifold proof, round metric, or recognition
homeomorphism is stored. -/
structure FiniteSmoothingReactionDecayDirectUniformBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3.{u, v}
      M
  movingGenericSuccessorInputs :
    FixedTargetMovingGenericSuccessorInputs3 M
  postRealizationGridCoherence :
    FixedTargetMovingPostRealizationGridCoherence3
      M movingGenericSuccessorInputs

/-- The finite smoothing solver constructs the selected smooth atlas; on that
atlas, eventual Hamilton pinching gives finite energy, while the generic
successor neighborhood and finite post-realization grid coherence give
unit-curvature recognition. -/
theorem FiniteSmoothingReactionDecayDirectUniformBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingReactionDecayDirectUniformBoundaryData3.{u, v} M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  let finiteNerveReduction :=
    @FiniteSmoothingReactionDecayDirectUniformBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingReactionDecayDirectUniformBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingReactionDecayDirectUniformBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let movingGenericSuccessorInputs :
      FixedTargetMovingGenericSuccessorInputs3 M :=
    @FiniteSmoothingReactionDecayDirectUniformBoundaryData3.movingGenericSuccessorInputs
      M _ _ ambientChartedSpace _ _ data
  let postRealizationGridCoherence :
      FixedTargetMovingPostRealizationGridCoherence3
        M movingGenericSuccessorInputs :=
    @FiniteSmoothingReactionDecayDirectUniformBoundaryData3.postRealizationGridCoherence
      M _ _ ambientChartedSpace _ _ data
  let simultaneousSmoothing :=
    plCompatibleAffineConjugacy
      |>.toFiniteNerveSimultaneousLocalConjugacySmoothing3
  obtain ⟨smoothData⟩ :=
    simultaneousSmoothing.nonempty_cInfinityLocalTransitionAtlasData3
  apply normalizedFlowTarget_elim_of_cInfinityLocalTransitionAtlasData3
    smoothData
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have unitRecognition : UnitConstantCurvatureSphereRecognition3 M :=
    unitConstantCurvatureSphereRecognition3_of_fixedTargetMovingInputs_postRealizationGridCoherence
      movingGenericSuccessorInputs postRealizationGridCoherence
  exact analytic.sphereConclusion unitRecognition

/-- Universal existence of the explicit finite-smoothing/reaction-decay
boundary data. -/
def UniversalFiniteSmoothingReactionDecayDirectUniformBoundaryData3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingReactionDecayDirectUniformBoundaryData3.{u, v} M)

/-- The universal finite smoothing, reaction-decay, moving-measure, and
direct-uniform Cartan provider implies the canonical topological Poincare
statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingReactionDecayDirectUniformBoundaryData3
    (provider :
      UniversalFiniteSmoothingReactionDecayDirectUniformBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
