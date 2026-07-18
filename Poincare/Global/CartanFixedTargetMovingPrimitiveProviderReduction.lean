import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary

/-!
# Primitive provider for fixed-target moving Cartan inputs

`FixedTargetMovingGenericSuccessorInputs3` is the minimal shared recognition
contract: it stores qualitative fixed-chart transition agreement, continuity
of the fixed-to-preferred derivative, generic source-normal local stability,
the exact target zero-section interior condition, and transferred-package
diagonal continuation.

This file gives a lower-level sufficient provider for that contract.  Instead
of assuming generic source-normal local stability, it asks for two independent
source facts:

* joint regularity of the generic source exponential family; and
* continuity at frozen centers of the preferred-to-fixed transition
  derivative.

The second fact produces the verified local operator-norm bound.  Together
with joint regularity, that bound produces generic source-normal local
stability through the existing stationary-chart reduction.  The fixed-chart
source agreement and fixed-to-preferred continuity clauses pass through
unchanged, as do the exact target zero-section and transferred-package
diagonal-continuation clauses.

No successor cover, equality neighborhood, grid coherence, or sphere
recognition is stored in the primitive package, and the minimal shared
contract is not modified.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingPrimitiveProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Primitive moving-chart facts for one constant-curvature source metric.

The two transition-continuity directions have distinct roles.  The
fixed-to-preferred direction upgrades subordinate ODE agreement to a
quantitative moving fixed-chart source package.  The preferred-to-fixed
direction controls source chart metrics and all dependent tangent
alignments. -/
structure FixedTargetMovingGenericSuccessorPrimitiveData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  subordinateFixedChartTransitionAgreement :
    SubordinateFixedChartTransitionAgreement g
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

namespace FixedTargetMovingGenericSuccessorPrimitiveData3

/-- Preferred-to-fixed derivative continuity supplies the stationary-chart
operator bound, which combines with generic joint regularity to give the
exact source-normal stability clause in the shared moving-input contract. -/
theorem genericSourceNormalLocalStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : FixedTargetMovingGenericSuccessorPrimitiveData3 g) :
    GenericSourceNormalLocalStability g := by
  apply
    genericSourceNormalLocalStability_of_jointRegularity_and_preferredToFixedTransitionDerivativeLocalBound
      data.genericJointRegularity
  exact
    preferredToFixedTransitionDerivativeLocalBound_of_continuousAtCenters
      data.preferredToFixedTransitionDerivativeContinuousAtCenters

end FixedTargetMovingGenericSuccessorPrimitiveData3

/-! ## Universal fixed-target provider -/

/-- Primitive data on every smooth constant-curvature target metric quantified
by `FixedTargetMovingGenericSuccessorInputs3`.

The instance and curvature quantifiers are intentionally identical to the
minimal shared provider, so this definition changes only the geometric data
requested after those instances have been installed. -/
def FixedTargetMovingGenericSuccessorPrimitiveInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorPrimitiveData3 g

/-- The primitive provider constructs the existing minimal fixed-target
moving-input contract.

Only `GenericSourceNormalLocalStability` is derived.  The remaining source,
target, and diagonal-continuation clauses are preserved literally. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_primitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive : FixedTargetMovingGenericSuccessorPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  let data := primitive g hcurv
  exact ⟨data.subordinateFixedChartTransitionAgreement,
    data.fixedToPreferredTransitionDerivativeContinuousAtCenters,
    data.genericSourceNormalLocalStability,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

/-- Consequently, the primitive provider also constructs the exact local
generic-successor cover consumed by rooted adaptive recognition. -/
theorem localGenericSuccessorDataCover_of_primitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive : FixedTargetMovingGenericSuccessorPrimitiveInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_fixedTargetMovingInputs3
    (fixedTargetMovingGenericSuccessorInputs3_of_primitiveInputs primitive)

end CartanFixedTargetMovingPrimitiveProviderReduction
end Poincare
