import Poincare.Global.CartanFixedTargetMovingPrimitiveProviderReduction
import Poincare.Global.CartanFixedChartTransitionAgreementSubordination

/-!
# Pointwise-package primitive provider for fixed-target moving Cartan inputs

The primitive fixed-target provider asks for fixed-chart transition agreement
subordinate to every neighborhood of every center.  A separate restriction
theorem shows that one proof-bearing transition package at each center already
implies that subordinate contract.

This file installs that theorem as a thin provider adapter.  It replaces only
the first field of the per-metric primitive package by pointwise transition-
package existence.  The two transition-derivative continuity fields, generic
joint regularity, exact target zero-section interior condition, and transferred
package diagonal continuation are retained literally.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingPointwisePrimitiveProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartTransitionAgreementSubordination
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingPrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Primitive moving-chart facts for one constant-curvature source metric,
with pointwise proof-bearing transition packages in place of the subordinate
transition-agreement quantifier. -/
structure FixedTargetMovingGenericSuccessorPointwisePrimitiveData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartTransitionAgreementPackage :
    PointwiseFixedChartTransitionAgreementPackage g
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

namespace FixedTargetMovingGenericSuccessorPointwisePrimitiveData3

/-- Restricting each chosen pointwise transition package supplies the first
field of the existing per-metric primitive provider.  Every other field is
copied without alteration. -/
def toPrimitiveData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : FixedTargetMovingGenericSuccessorPointwisePrimitiveData3 g) :
    FixedTargetMovingGenericSuccessorPrimitiveData3 g :=
  ⟨subordinateFixedChartTransitionAgreement_of_pointwisePackage
      data.pointwiseFixedChartTransitionAgreementPackage,
    data.fixedToPreferredTransitionDerivativeContinuousAtCenters,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorPointwisePrimitiveData3

/-! ## Universal fixed-target provider -/

/-- Pointwise-package primitive data on every smooth constant-curvature
target metric, with the same instance and curvature quantifiers as the
existing primitive and minimal fixed-target providers. -/
def FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorPointwisePrimitiveData3 g

/-- The pointwise-package provider constructs the existing primitive
fixed-target provider by restricting its packages on demand. -/
theorem fixedTargetMovingGenericSuccessorPrimitiveInputs3_of_pointwisePrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive : FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorPrimitiveInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (primitive g hcurv).toPrimitiveData

/-- Consequently, pointwise transition-package existence also constructs the
minimal shared fixed-target moving-input contract. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive : FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_primitiveInputs
    (fixedTargetMovingGenericSuccessorPrimitiveInputs3_of_pointwisePrimitiveInputs
      primitive)

/-- The pointwise-package provider therefore supplies the exact local generic
successor-data cover consumed by rooted adaptive recognition. -/
theorem localGenericSuccessorDataCover_of_pointwisePrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive : FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_primitiveInputs
    (fixedTargetMovingGenericSuccessorPrimitiveInputs3_of_pointwisePrimitiveInputs
      primitive)

end CartanFixedTargetMovingPointwisePrimitiveProviderReduction
end Poincare
