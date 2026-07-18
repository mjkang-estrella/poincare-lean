import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction

/-!
# Positive-time overlap provider for fixed-target moving Cartan inputs

This adapter replaces the target-chart ODE primitive field of the existing
fixed-target moving boundary by the still lower, honest path-retention input:
four ordinary overlap memberships only at strictly positive times.  The
fixed anchor slice is subordinated to its open chart/cutoff-one locus, so all
four time-zero memberships are theorems.

The remaining fixed-target fields pass through literally.  In particular,
this module does not alter the generic joint regularity, target-side chart
data, or diagonal-continuation residuals.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanFixedChartGenericInverseEndpointODEComparison
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
open CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
open CartanFixedTargetMovingPointwisePrimitiveProviderReduction
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-! ## Per-center conversion -/

/-- At each center, choose one fixed-chart package with transition-derivative
continuity and the four unchanged overlap residuals only on the strictly
positive comparison interval. -/
def PointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ContinuousOn (fixedToPreferredTransitionDerivative x₀)
          C.rawLocalFamily.anchors ∧
        C.GenericInverseEndpointODEPositiveTimeOverlapProvider

/-- Fixed-cutoff subordination preserves transition continuity and turns the
positive-time provider into the existing target-chart ODE comparison
provider. -/
theorem pointwiseFixedChartGenericInverseEndpointODEData_of_positiveTimeOverlap
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hdata :
      PointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData g) :
    PointwiseFixedChartGenericInverseEndpointODEData g := by
  intro x₀
  rcases hdata x₀ with ⟨C, htransition, hpositive⟩
  let C' := C.restrictToFixedAnchorCutoffOne
  have htransition' : ContinuousOn
      (fixedToPreferredTransitionDerivative x₀)
      C'.rawLocalFamily.anchors := by
    exact htransition.mono
      C.restrictToFixedAnchorCutoffOne_rawLocalFamily_anchors_subset_original
  have hcomparison : C'.GenericInverseEndpointODEComparisonProvider := by
    simpa [C'] using
      C.genericInverseEndpointODEComparisonProvider_of_positiveTimeOverlap
        hpositive
  exact ⟨C', htransition', hcomparison⟩

/-! ## Metric-level five-field adapter -/

/-- Primitive moving-chart facts for one constant-curvature source metric,
with the moving endpoint reduced to strictly-positive-time overlap retention
on a cutoff-subordinated fixed-chart package. -/
structure
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  pointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData :
    PointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData g
  genericJointRegularity : GenericJointRegularity g
  preferredToFixedTransitionDerivativeContinuousAtCenters :
    PreferredToFixedTransitionDerivativeContinuousAtCenters (M := M)
  targetZeroSectionInterior : ∀ p : RoundSphere3,
    (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus
  transferredPackageDiagonalContinuation :
    TransferredSuccessorPackageDiagonalContinuation g

namespace FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3

/-- Convert only the first field through the positive-time ODE comparison;
copy the other four fixed-target fields definitionally. -/
def toGenericInverseEndpointODEPrimitiveData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3
        g) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveData3 g :=
  ⟨pointwiseFixedChartGenericInverseEndpointODEData_of_positiveTimeOverlap
      data.pointwiseFixedChartGenericInverseEndpointODEPositiveTimeOverlapData,
    data.genericJointRegularity,
    data.preferredToFixedTransitionDerivativeContinuousAtCenters,
    data.targetZeroSectionInterior,
    data.transferredPackageDiagonalContinuation⟩

end FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3

/-! ## Universal fixed-target provider -/

/-- Positive-time overlap data on every smooth constant-curvature target
metric. -/
def
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        HasConstantSectionalCurvature3 g 1 →
          FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapData3
            g

/-- Convert the positive-time fixed-target provider to the existing
ODE-primitive input contract. -/
theorem
    fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (positive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
        M) :
    FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3 M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  exact (positive g hcurv).toGenericInverseEndpointODEPrimitiveData

/-- The same positive-time provider supplies the minimal shared moving-input
contract through the definitionally fixed ODE-primitive conversion. -/
theorem
    fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPositiveTimeOverlapInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (positive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
        M) :
    FixedTargetMovingGenericSuccessorInputs3 M :=
  fixedTargetMovingGenericSuccessorInputs3_of_genericInverseEndpointODEPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
      positive)

/-- The positive-time input also reaches the exact local generic successor
cover consumed by rooted recognition. -/
theorem
    localGenericSuccessorDataCover_of_genericInverseEndpointODEPositiveTimeOverlapInputs
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (positive :
      FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3
        M) :
    ∀ [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (g : ClosedSmoothRiemannianMetric 3 M),
          ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
            LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_genericInverseEndpointODEPrimitiveInputs
    (fixedTargetMovingGenericSuccessorGenericInverseEndpointODEPrimitiveInputs3_of_positiveTimeOverlapInputs
      positive)

end CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction
end Poincare
