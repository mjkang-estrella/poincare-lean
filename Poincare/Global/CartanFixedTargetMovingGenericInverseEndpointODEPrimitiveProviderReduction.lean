import Poincare.Global.CartanFixedChartGenericInverseEndpointODEComparison
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction

/-!
# ODE-comparison primitive provider for fixed-target moving Cartan inputs

This adapter replaces the generic-inverse endpoint identity in the current
five-field fixed-target provider by target-chart ODE comparison data.  ODE
uniqueness constructs the identity; the remaining four fields pass through
unchanged.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartGenericInverseEndpointODEComparison
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanSourceExponential

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Primitive moving-chart facts for one constant-curvature source metric,
with the moving fixed-chart endpoint supplied by a common ODE comparison
rather than by endpoint equality. -/
structure FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartGenericInverseEndpointODEData :
    PointwiseFixedChartGenericInverseEndpointODEData g
  genericJointRegularity : GenericJointRegularity g
  preferredToFixedTransitionDerivativeContinuousAtCenters :
    PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)
  targetZeroSectionInterior : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus
  transferredPackageDiagonalContinuation :
    TransferredSuccessorPackageDiagonalContinuation g

namespace FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3

/-- ODE uniqueness constructs only the generic-inverse endpoint identity;
the other primitive fields are copied literally. -/
def toGenericInverseEndpointPrimitiveData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3 g) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3 g :=
  ⟨pointwiseGenericInverseEndpointData_of_odeComparison
      data.pointwiseFixedChartGenericInverseEndpointODEData,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3

/-! ## Universal fixed-target provider -/

/-- ODE-comparison primitive data on every smooth constant-curvature target
metric. -/
def FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3 g

/-- Construct the verified generic-inverse endpoint provider by ODE
uniqueness at every fixed target. -/
theorem fixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3_of_odePrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (primitive g hcurv).toGenericInverseEndpointPrimitiveData

/-- Consequently the ODE-comparison provider constructs the minimal shared
fixed-target moving-input contract. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3_of_odePrimitiveInputs
      primitive)

/-- The same ODE data supply the local generic successor-data cover consumed
by rooted recognition. -/
theorem localGenericSuccessorDataCover_of_genericInverseEndpointODEPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_genericInverseEndpointPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3_of_odePrimitiveInputs
      primitive)

end CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
end Poincare
