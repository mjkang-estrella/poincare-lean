import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein
import Poincare.Global.CartanFixedTargetMovingPointwisePrimitiveProviderReduction
import Poincare.Global.CartanGenericPostRealizationCompactHistoryReduction
import Poincare.Global.SmoothabilityPLCompatibleAffineConjugacy

/-!
# Finite-traceless-energy and compact-history Poincare boundary

This file combines the strongest current producer-style reductions on one
compact simply connected topological `3`-manifold.

* A finite nerve and its PL-compatible affine-conjugacy package construct an
  actual `C∞` atlas.
* Compact normalized-flow data with finite total traceless-Ricci energy
  construct finite absolute dissipation, a positive Einstein metric, and a
  unit-sectional-curvature metric.
* Pointwise fixed-chart transition packages, the two transition-derivative
  continuity directions, source joint regularity, target zero-section
  interior, and package diagonal continuation construct the moving generic
  successor inputs.
* Compactly parameterized sequences of actual realized-grid
  precertificates, with positive lower-semicontinuous common radii and
  vanishing finite edge maxima, construct post-realization grid coherence.

The compact-history field below is definitionally tied to the moving-input
contract derived from the pointwise primitive provider.  Thus the record
cannot store an unrelated moving provider or a separately assumed coherence
proof.  It stores no selected smooth atlas, manifold instance, finite
dissipation proof, Einstein metric, unit-curvature recognition theorem, or
sphere homeomorphism.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericPostRealizationCompactHistoryReduction
open SmoothabilityPLCompatibleAffineConjugacy

/-- The producer-only finite-smoothing, finite-traceless-energy,
pointwise-moving, compact-history boundary on a fixed topological
`3`-manifold.

The last field depends on the exact moving-input value constructed from the
preceding pointwise primitive provider; no second moving-input field is
present. -/
structure
    FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M] where
  finiteNerveReduction :
    SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M
  plCompatibleAffineConjugacy :
    FiniteNervePLCompatibleAffineConjugacy3 finiteNerveReduction
  analytic :
    FixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
      M
  pointwiseMovingPrimitiveInputs :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M
  compactHistoryFeedback :
    FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
      (fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
        pointwiseMovingPrimitiveInputs)

/-- Finite affine-conjugacy smoothing installs the selected atlas; the
pointwise primitive provider constructs its moving generic successor inputs;
compact histories construct the exact post-realization grid coherence; and
finite traceless energy reaches the analytic sphere endpoint through the
resulting unit-curvature recognition theorem. -/
theorem
    FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ambientChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.{u, v}
        M) :
    Nonempty (M ≃ₜ ThreeSphere) := by
  let finiteNerveReduction :=
    @FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.finiteNerveReduction
      M _ _ ambientChartedSpace _ _ data
  let plCompatibleAffineConjugacy :=
    @FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.plCompatibleAffineConjugacy
      M _ _ ambientChartedSpace _ _ data
  let analytic :
      FixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M :=
    @FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.analytic
      M _ _ ambientChartedSpace _ _ data
  let pointwiseMovingPrimitiveInputs :
      FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M :=
    @FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.pointwiseMovingPrimitiveInputs
      M _ _ ambientChartedSpace _ _ data
  let simultaneousSmoothing :=
    plCompatibleAffineConjugacy
      |>.toFiniteNerveSimultaneousLocalConjugacySmoothing3
  obtain ⟨smoothData⟩ :=
    simultaneousSmoothing.nonempty_cInfinityLocalTransitionAtlasData3
  let movingGenericSuccessorInputs :
      FixedTargetMovingGenericSuccessorInputs3 M :=
    fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
      pointwiseMovingPrimitiveInputs
  let compactHistoryFeedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M
        movingGenericSuccessorInputs :=
    @FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.compactHistoryFeedback
      M _ _ ambientChartedSpace _ _ data
  let postRealizationGridCoherence :
      FixedTargetMovingPostRealizationGridCoherence3
        M movingGenericSuccessorInputs :=
    fixedTargetMovingPostRealizationGridCoherence3_of_compactHistoryFeedback
      (inputs := movingGenericSuccessorInputs) compactHistoryFeedback
  apply normalizedFlowTarget_elim_of_cInfinityLocalTransitionAtlasData3
    smoothData
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have unitRecognition : UnitConstantCurvatureSphereRecognition3 M :=
    unitConstantCurvatureSphereRecognition3_of_fixedTargetMovingInputs_postRealizationGridCoherence
      movingGenericSuccessorInputs postRealizationGridCoherence
  exact analytic.sphereConclusion unitRecognition

/-- Universal existence of the producer-only finite-smoothing,
finite-traceless-energy, pointwise-moving, compact-history boundary data. -/
def
    UniversalFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3 :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty
        (FiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.{u, v}
          M)

/-- A universal producer for this boundary implies the repository's
canonical topological Poincare statement. -/
theorem
    poincareConjectureStatement_of_universalFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3
    (provider :
      UniversalFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundaryData3.{u, v}) :
    PoincareConjectureStatement.{u} := by
  intro M _topologicalSpace _t2Space _ambientChartedSpace
    _simplyConnectedSpace _compactSpace
  rcases provider M with ⟨data⟩
  exact data.sphereConclusion

end Poincare
