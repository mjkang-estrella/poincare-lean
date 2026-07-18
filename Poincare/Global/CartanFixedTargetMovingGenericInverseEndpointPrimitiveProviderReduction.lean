import Poincare.Global.CartanFixedChartGenericInverseEndpointReduction
import Poincare.Global.CartanFixedTargetMovingPointwisePrimitiveProviderReduction

/-!
# Generic-inverse endpoint primitive provider for fixed-target Cartan inputs

This adapter installs the generic-inverse endpoint reduction at the universal
fixed-target boundary.  Its per-center fixed-chart datum contains:

* continuity of the fixed-to-preferred transition derivative on one open
  anchor slice; and
* the single manifold equality between the fixed-chart selector endpoint and
  the inverse evaluation of the generic normal family.

Joint generic regularity generates the positive radius and endpoint-domain
facts.  Continuity on the open anchor slice also implies the centerwise
continuity used by the later quantitative operator-bound reduction, so that
field is not repeated in the primitive package below.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartGenericInverseEndpointReduction
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Continuity on the chosen open anchor slice at every center already gives
the centerwise continuity contract used to obtain local operator bounds. -/
theorem fixedToPreferredTransitionDerivativeContinuousAtCenters_of_pointwiseGenericInverseEndpointData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hdata : PointwiseFixedChartGenericInverseEndpointData g) :
    FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M) := by
  intro x₀
  rcases hdata x₀ with ⟨C, hcontinuous, _hinverse⟩
  exact hcontinuous.continuousAt
    (C.rawLocalFamily.isOpen_anchors.mem_nhds
      C.center_mem_rawLocalFamily_anchors)

/-- Primitive moving-chart facts for one constant-curvature source metric,
with the fixed-chart endpoint comparison reduced to one generic-inverse
manifold identity. -/
structure FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartGenericInverseEndpointData :
    PointwiseFixedChartGenericInverseEndpointData g
  genericJointRegularity : GenericJointRegularity g
  preferredToFixedTransitionDerivativeContinuousAtCenters :
    PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)
  targetZeroSectionInterior : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus
  transferredPackageDiagonalContinuation :
    TransferredSuccessorPackageDiagonalContinuation g

namespace FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3

/-- Generate the pointwise transition package and the formerly separate
fixed-to-preferred centerwise continuity field; copy the other primitive
fields literally. -/
def toPointwisePrimitiveData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3 g) :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveData3 g :=
  ⟨pointwiseFixedChartTransitionAgreementPackage_of_genericInverseEndpointData
      data.genericJointRegularity
      data.pointwiseFixedChartGenericInverseEndpointData,
    fixedToPreferredTransitionDerivativeContinuousAtCenters_of_pointwiseGenericInverseEndpointData
      data.pointwiseFixedChartGenericInverseEndpointData,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3

/-! ## Universal fixed-target provider -/

/-- Generic-inverse endpoint primitive data on every smooth
constant-curvature target metric. -/
def FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveData3 g

/-- The generic-inverse endpoint provider constructs the existing pointwise
primitive fixed-target provider. -/
theorem fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_genericInverseEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (primitive g hcurv).toPointwisePrimitiveData

/-- Consequently, the same five-field primitive provider constructs the
minimal shared fixed-target moving-input contract. -/
theorem fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_pointwisePrimitiveInputs
    (fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_genericInverseEndpointPrimitiveInputs
      primitive)

/-- The generic-inverse endpoint provider supplies the exact local generic
successor-data cover consumed by rooted recognition. -/
theorem localGenericSuccessorDataCover_of_genericInverseEndpointPrimitiveInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (primitive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointPrimitiveInputs3 M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_pointwisePrimitiveInputs
    (fixedTargetMovingGenericSuccessorPointwisePrimitiveInputs3_of_genericInverseEndpointPrimitiveInputs
      primitive)

end CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
end Poincare
