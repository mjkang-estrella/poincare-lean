import Poincare.Global.CartanFixedTargetMovingPointwisePrimitiveProviderReduction
import Poincare.Global.CartanFixedChartTransitionAgreementContinuityReduction

/-!
# Continuity/endpoint primitive provider for fixed-target moving Cartan inputs

The pointwise primitive provider asks for an existing transition-agreement
package at every center.  The fixed-chart continuity reduction shows that it
is enough to retain, on the same fixed-chart package, continuity of the
fixed-to-preferred transition derivative and the unchanged positive-time
endpoint agreement at a positive radius.

This file installs that reduction at the universal fixed-target boundary.  It
replaces only the first field of the pointwise primitive data package.  The
two transition-derivative continuity fields, generic joint regularity, exact
target zero-section interior condition, and transferred-package diagonal
continuation are copied literally.  No grid, realization, or recognition
data is introduced.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingContinuityEndpointPrimitiveProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartTransitionAgreementContinuityReduction
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Primitive moving-chart facts for one constant-curvature source metric,
using per-center fixed-chart continuity/endpoint data rather than already
assembled pointwise transition-agreement packages. -/
structure FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartTransitionAgreementContinuityEndpointData :
    PointwiseFixedChartTransitionAgreementContinuityEndpointData g
  fixedToPreferredTransitionDerivativeContinuousAtCenters :
    FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M)
  genericJointRegularity :
    CartanSourceExponential.GenericJointRegularity g
  preferredToFixedTransitionDerivativeContinuousAtCenters :
    PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)
  targetZeroSectionInterior : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus
  transferredPackageDiagonalContinuation :
    TransferredSuccessorPackageDiagonalContinuation g

namespace FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveData3

/-- Assemble only the first field into the existing pointwise primitive data;
the remaining five fields are preserved literally. -/
def toPointwisePrimitiveData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data :
      FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveData3 g) :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveData3 g :=
  ⟨pointwiseFixedChartTransitionAgreementPackage_of_continuityEndpointData
      data.pointwiseFixedChartTransitionAgreementContinuityEndpointData,
    data.fixedToPreferredTransitionDerivativeContinuousAtCenters,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveData3

/-! ## Universal fixed-target provider -/

/-- Continuity/endpoint primitive data on every smooth constant-curvature
target metric, with the same instance and curvature quantifiers as the
existing fixed-target providers. -/
def FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveData3 g

/-- The continuity/endpoint provider constructs the existing pointwise
primitive fixed-target provider, preserving the metric selected at each
curvature instance. -/
theorem fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_continuityEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (primitive g hcurv).toPointwisePrimitiveData

/-- Consequently, continuity/endpoint primitive inputs construct the minimal
shared fixed-target moving-input contract. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_continuityEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
    (fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_continuityEndpointPrimitiveInputs
      primitive)

/-- The same primitive inputs supply the exact local generic successor-data
cover, without storing any downstream grid or recognition data. -/
theorem localGenericSuccessorDataCover_of_continuityEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorContinuityEndpointPrimitiveInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_pointwisePrimitiveInputs
    (fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_continuityEndpointPrimitiveInputs
      primitive)

end CartanFixedTargetMovingContinuityEndpointPrimitiveProviderReduction
end Poincare
