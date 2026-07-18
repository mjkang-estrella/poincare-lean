import Poincare.Global.CartanFixedChartTransitionAgreementSubordination

/-!
# Fixed-chart transition agreement from moving-derivative continuity

The fixed-chart product inverse already carries a jointly continuous raw
inverse velocity.  Its transported velocity is obtained by applying the
fixed-to-preferred chart-transition derivative at the moving anchor.  This
file records the exact composition argument: continuity of that operator
family on the retained anchors implies joint continuity of the transported
inverse on the package's joint endpoint locus.

The remaining positive-time endpoint comparison is not altered or renamed.
A same-package data structure stores it together with a positive radius and
the moving-derivative continuity premise.  Only the transported-velocity
continuity field is derived when constructing the existing transition-
agreement package.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Function Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanGenericSuccessorDataMovingPersistenceReduction

/-- Continuity of the fixed-to-preferred transition derivative on the
retained anchors combines with continuity of the raw inverse velocity to give
the exact joint transported-velocity continuity predicate. -/
theorem transitionVelocityJointContinuity_of_fixedToPreferredTransitionDerivative_continuousOn
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htransition : ContinuousOn
      (fixedToPreferredTransitionDerivative x₀)
      C.rawLocalFamily.anchors) :
    C.TransitionVelocityJointContinuity := by
  have hoperator : ContinuousOn
      (fun q : M × M => fixedToPreferredTransitionDerivative x₀ q.1)
      C.rawLocalFamily.sourceLocus :=
    htransition.comp continuous_fst.continuousOn
      (fun q hq => C.rawLocalFamily.sourceLocus_fst q hq)
  have happly : ContinuousOn
      (fun q : M × M =>
        fixedToPreferredTransitionDerivative x₀ q.1
          (C.rawLocalFamily.normal q))
      C.rawLocalFamily.sourceLocus :=
    hoperator.clm_apply C.rawLocalFamily.continuousOn_normal
  simpa only [TransitionVelocityJointContinuity, transportedNormal,
    fixedToAnchorVelocity, fixedToPreferredTransitionDerivative] using happly

/-- Same-fixed-chart data sufficient for an existing transition-agreement
package.  Endpoint agreement is retained literally; only transported-
velocity continuity is reduced to continuity of the moving operator family.

This structure is Type-valued because its positive radius is used to
construct the Type-valued `TransitionAgreementPackage`. -/
structure TransitionAgreementContinuityEndpointData
    (C : FixedChartAnchorEndpointPackage g x₀) where
  fixedToPreferredTransitionDerivativeContinuousOn : ContinuousOn
    (fixedToPreferredTransitionDerivative x₀)
    C.rawLocalFamily.anchors
  radius : ℝ
  radius_pos : 0 < radius
  fixedTimeEndpoint : C.FixedPositiveTimeEndpointAgreement radius

namespace TransitionAgreementContinuityEndpointData

/-- Package the unchanged radius and endpoint agreement, deriving precisely
the transported-velocity joint-continuity field. -/
def toTransitionAgreementPackage
    {C : FixedChartAnchorEndpointPackage g x₀}
    (data : C.TransitionAgreementContinuityEndpointData) :
    C.TransitionAgreementPackage where
  radius := data.radius
  radius_pos := data.radius_pos
  jointContinuity :=
    C.transitionVelocityJointContinuity_of_fixedToPreferredTransitionDerivative_continuousOn
      data.fixedToPreferredTransitionDerivativeContinuousOn
  fixedTimeEndpoint := data.fixedTimeEndpoint

end TransitionAgreementContinuityEndpointData
end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport

/-! ## Per-center provider -/

namespace CartanFixedChartTransitionAgreementContinuityReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanFixedChartTransitionAgreementSubordination
open CartanSourceExponentialLocalFamilyTransport

/-- At every center, one fixed-chart package carrying moving-derivative
continuity and positive-time endpoint agreement.  `Nonempty` preserves the
Type-valued same-package witness under this Prop-valued provider. -/
def PointwiseFixedChartTransitionAgreementContinuityEndpointData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      Nonempty C.TransitionAgreementContinuityEndpointData

/-- The per-center continuity/endpoint provider constructs the pointwise
transition-agreement package provider without changing the chosen fixed-chart
package. -/
theorem pointwiseFixedChartTransitionAgreementPackage_of_continuityEndpointData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hdata : PointwiseFixedChartTransitionAgreementContinuityEndpointData g) :
    PointwiseFixedChartTransitionAgreementPackage g := by
  intro x₀
  rcases hdata x₀ with ⟨C, ⟨data⟩⟩
  exact ⟨C, ⟨data.toTransitionAgreementPackage⟩⟩

end CartanFixedChartTransitionAgreementContinuityReduction
end Poincare
