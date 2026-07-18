import Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction

/-!
# Tail-overlap provider for fixed-target moving Cartan inputs

The initial portion of the fixed-chart selector stays in the full overlap
locus automatically.  This adapter therefore replaces the positive-time
moving input by the same four path-retention residuals only after the chosen
`initialOverlapTime`.

The tail provider first constructs the already verified positive-time
provider.  Every other fixed-target field is copied literally.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartGenericInverseEndpointODEComparison
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-! ## Per-center conversion -/

/-- At each center, transition-derivative continuity together with only the
post-`initialOverlapTime` path-retention residual. -/
def PointwiseFixedChartGenericInverseEndpointODETailOverlapData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ContinuousOn (fixedToPreferredTransitionDerivative x₀)
          C.rawLocalFamily.anchors ∧
        C.GenericInverseEndpointODETailOverlapProvider

/-- Automatic initial retention turns the tail-only per-center input into the
verified positive-time per-center input without changing the package. -/
theorem
    pointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData_of_tail
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hdata : PointwiseFixedChartGenericInverseEndpointODETailOverlapData g) :
    PointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData g := by
  intro x₀
  rcases hdata x₀ with ⟨C, htransition, htail⟩
  exact ⟨C, htransition,
    C.genericInverseEndpointODEPositiveTimeOverlapProvider_of_tail htail⟩

/-! ## Metric-level five-field adapter -/

/-- Fixed-target primitive data with the moving endpoint reduced to the exact
tail overlap residual. -/
structure
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartGenericInverseEndpointODETailOverlapData :
    PointwiseFixedChartGenericInverseEndpointODETailOverlapData g
  genericJointRegularity : GenericJointRegularity g
  preferredToFixedTransitionDerivativeContinuousAtCenters :
    PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)
  targetZeroSectionInterior : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus
  transferredPackageDiagonalContinuation :
    TransferredSuccessorPackageDiagonalContinuation g

namespace FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapData3

/-- Convert only the tail field; copy the remaining four fixed-target fields
definitionally. -/
def toPositiveTimeOverlapData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapData3
        g) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3
      g :=
  ⟨pointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData_of_tail
      data.pointwiseFixedChartGenericInverseEndpointODETailOverlapData,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapData3

/-! ## Universal fixed-target provider -/

def FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapData3
            g

/-- Tail-only universal inputs construct the verified positive-time universal
inputs. -/
theorem
    fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3_of_tailInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (tail :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
        M) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (tail g hcurv).toPositiveTimeOverlapData

/-- Tail-only universal inputs construct the old ODE-primitive input contract
through the verified positive-time adapter. -/
theorem
    fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (tail :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
        M) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M :=
  fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3_of_tailInputs
      tail)

/-- The tail-only provider supplies the minimal shared moving-input contract. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODETailOverlapInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (tail :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
        M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
      tail)

/-- The same tail-only input reaches the exact local generic successor-data
cover consumed by rooted recognition. -/
theorem localGenericSuccessorDataCover_of_genericInverseEndpointODETailOverlapInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (tail :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODETailOverlapInputs3
        M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_genericInverseEndpointODEPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_tailInputs
      tail)

end CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
end Poincare
