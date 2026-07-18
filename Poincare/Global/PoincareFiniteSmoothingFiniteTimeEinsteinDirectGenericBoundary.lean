import Poincare.Global.NormalizedFlowCompactFixedTargetEventualCoerciveGapPositiveEinstein
import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary
import Poincare.Global.SmoothabilityPLCompatibleAffineConjugacy

/-!
# Finite smoothing and finite-time Einstein direct-generic boundary

This module combines three independent, proof-bearing boundaries on one
compact simply connected topological `3`-manifold:

1. pointwise PL-compatible affine-equivalence germs construct a selected
   `C∞` atlas after compact finite-subcover bookkeeping;
2. an eventual strict scalar-variance/traceless-energy gap on a continuous
   compact metric family proves finite dissipation, then constructs a
   positive Einstein metric and hence a unit-sectional-curvature metric; and
3. moving fixed-chart ODE and chart-transition data construct the generic
   successor cover, while finite post-realization adaptive grid coherence
   recognizes every such unit metric as the round sphere.

The analytic route constructs finite absolute dissipation from an eventual
coercive gap and compact moving-measure continuity; it does not store that
integrability as an input.  This file does not import or store the
quantitative near-round-tail analytic package.  Likewise, the Cartan route
constructs its generic local cover: no raw successor neighborhood,
canonical-family neighborhood, or canonical-to-generic bridge is retained.

The boundary structure stores neither a selected atlas, a manifold instance,
a positive Einstein metric, a unit-curvature recognition theorem, nor a sphere
homeomorphism.  Each of those objects is constructed in the theorem below.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open SmoothabilityPLCompatibleAffineConjugacy

/-- The finite-smoothing, finite-time-Einstein, direct-generic boundary on a
fixed compact simply connected topological `3`-manifold.

The first two fields are the finite nerve and its pointwise PL-compatible
affine-conjugacy residual.  All remaining data are polymorphic in the smooth
structure constructed from those germs. -/
structure FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
      M
  movingGenericSuccessorInputs :
    FixedTargetMovingGenericSuccessorInputs3 M
  postRealizationGridCoherence :
    FixedTargetMovingPostRealizationGridCoherence3
      M movingGenericSuccessorInputs

/-- PL-compatible affine germs construct the atlas; eventual-gap finite-time
concentration constructs a unit-curvature metric; and finite actual-grid radii
recognize it as the unit `3`-sphere. -/
theorem
    FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.{u, v} M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  let finiteNerveReduction :=
    @FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let movingGenericSuccessorInputs :
      FixedTargetMovingGenericSuccessorInputs3 M :=
    @FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.movingGenericSuccessorInputs
      M _ _ ambientChartedSpace _ _ data
  let postRealizationGridCoherence :
      FixedTargetMovingPostRealizationGridCoherence3
        M movingGenericSuccessorInputs :=
    @FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.postRealizationGridCoherence
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

/-- Universal existence of the input-only finite-smoothing,
finite-time-Einstein, direct-generic boundary data. -/
def UniversalFiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.{u, v} M)

/-- A universal finite-smoothing, finite-time-Einstein, direct-generic
provider implies the repository's canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3
    (provider :
      UniversalFiniteSmoothingFiniteTimeEinsteinDirectGenericBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
