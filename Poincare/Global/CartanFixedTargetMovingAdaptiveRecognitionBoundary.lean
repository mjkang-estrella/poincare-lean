import Poincare.Global.RoundSphereGenericCanonicalAgreementLocusReduction
import Poincare.Global.CartanGenericRootedAdaptiveFiniteGridRecognition

/-!
# Fixed-target Cartan recognition from moving-chart inputs

This file combines the two strongest nonuniform Cartan reductions:

* the generic successor-data cover is constructed from subordinate
  fixed-chart ODE agreement, continuity of the moving chart-transition
  derivative, generic source-normal stability, target chart agreement near
  the complete zero section, and an explicit package-continuation open locus;
* successor-germ equality is proved only on each finite realized overlap
  grid, using the common minimum of the actual constant-curvature radii on
  that grid.

The resulting fixed-target boundary contains neither a raw generic-data
neighborhood, a canonical-to-generic bridge, a global successor-equality
neighborhood, nor local uniformity over moving successor data.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare
namespace CartanFixedTargetMovingAdaptiveRecognitionBoundary

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanGenericRootedAdaptiveFiniteGridRecognition
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction
open RoundSphereGenericCanonicalAgreementLocusReduction

/-- Fixed-target geometric inputs from which the exact local generic-data
cover is constructed.

The proof-carrying input is requested only after a selected smooth atlas has
installed its manifold instances.  None of the five clauses mentions a
successor equality or a sphere-recognition conclusion. -/
def FixedTargetMovingGenericSuccessorInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          SubordinateFixedChartTransitionAgreement g ∧
          FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M) ∧
          GenericSourceNormalLocalStability g ∧
          (∀ p : RoundSphere3,
            (p, (0 : ClosedSmoothModel 3)) ∈
              interior genericCanonicalChartAgreementLocus) ∧
          TransferredSuccessorPackageDiagonalContinuation g

/-- The exact target-local generic successor-data cover constructed from the
five moving-chart inputs. -/
theorem localGenericSuccessorDataCover_of_fixedTargetMovingInputs3
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (inputs : FixedTargetMovingGenericSuccessorInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g _hcurv
  rcases inputs g _hcurv with
    ⟨htransition, htransitionContinuous, hsource,
      htargetZeroInterior, hpackageDiagonal⟩
  exact
    localGenericSuccessorDataCover_of_transitionAgreement_of_continuousAtCenters_of_targetZeroInterior_of_packageDiagonalContinuation
      htransition htransitionContinuous hsource
        htargetZeroInterior hpackageDiagonal

/-- Honest finite adaptive-feedback input after the moving-chart package has
constructed its exact generic successor radius.

For every constant-curvature metric, the completion chooses one mesh and
actual finite-grid coherence at the exact endpoint determined by the
constructed cover. -/
def FixedTargetMovingPostRealizationGridCoherence3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (inputs : FixedTargetMovingGenericSuccessorInputs3 M) : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          let dataStability :=
            localGenericSuccessorDataCover_of_fixedTargetMovingInputs3
              inputs g hcurv
          let successor :=
            CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly.uniformGenericSuccessorRadiusCertificateOfNeighborhood
              g dataStability.toUniversalSuccessorDataNeighborhood
          let endpoint := rootedEndpointOfUniformGenericSuccessorRadius
            successor
          ∃ mesh : ℝ,
            ∃ hmesh : 0 < mesh,
              Nonempty
                (GenericUniformRadiusPostRealizationGridCoherence
                  successor endpoint hcurv hmesh)

/-- Moving-chart successor construction plus finite actual-grid feedback
gives the complete unit-curvature sphere-recognition function. -/
theorem unitConstantCurvatureSphereRecognition3_of_fixedTargetMovingInputs_postRealizationGridCoherence
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (inputs : FixedTargetMovingGenericSuccessorInputs3 M)
    (completion : FixedTargetMovingPostRealizationGridCoherence3 M inputs) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        UnitConstantCurvatureSphereRecognition3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  exact
    unitConstantCurvatureSphereRecognition3_of_localGenericSuccessorDataCover_postRealizationGridCoherence
      (localGenericSuccessorDataCover_of_fixedTargetMovingInputs3 inputs)
      completion

end CartanFixedTargetMovingAdaptiveRecognitionBoundary
end Poincare
