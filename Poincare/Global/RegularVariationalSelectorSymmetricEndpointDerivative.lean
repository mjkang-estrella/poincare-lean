import Poincare.Global.RegularVariationalSelectorEndpointDerivative
import Poincare.Global.PicardLindelofRegularSelectorTimeReversal

/-!
# Symmetric-time endpoint derivative for a regular variational selector

The positive endpoint residual theorem extends to the negative protected
half interval by applying it to the definitionally time-reversed retained
selector.  Thus one regular first-variational family differentiates its base
endpoint map on both sides of relative time zero.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section SymmetricEndpointDerivative

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ q : X} {t : ℝ}

/-- The negative-time half of the endpoint derivative theorem, obtained by
reversing the same retained selector rather than choosing a second family. -/
theorem projectedEndpoint_hasFDerivAt_of_nonpos
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Icc (-(H.epsilon / 2)) 0) :
    HasFDerivAt (fun y : X ↦ H.projectFirstVariational.selector y t)
      (H.selector (q, ContinuousLinearMap.id ℝ X) t).2 q := by
  let Hrev : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fun x : X ↦ -F x))
      (x₀, ContinuousLinearMap.id ℝ X) :=
    H.reverseTimeFirstVariational
  have hqRev : q ∈ ball x₀ (Hrev.initialRadius : ℝ) := by
    simpa only [Hrev, reverseTimeFirstVariational] using hq
  have htRev : -t ∈ Icc (0 : ℝ) (Hrev.epsilon / 2) := by
    have hraw : -t ∈ Icc (0 : ℝ) (H.epsilon / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [Hrev, reverseTimeFirstVariational] using hraw
  have h := Hrev.projectedEndpoint_hasFDerivAt hqRev htRev
  simpa only [Hrev, reverseTimeFirstVariational,
    projectFirstVariational_selector, neg_neg] using h

/-- Endpoint differentiability on the full protected symmetric half
interval. -/
theorem projectedEndpoint_hasFDerivAt_symmetric
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Icc (-(H.epsilon / 2)) (H.epsilon / 2)) :
    HasFDerivAt (fun y : X ↦ H.projectFirstVariational.selector y t)
      (H.selector (q, ContinuousLinearMap.id ℝ X) t).2 q := by
  by_cases hnonneg : 0 ≤ t
  · exact H.projectedEndpoint_hasFDerivAt hq ⟨hnonneg, ht.2⟩
  · exact H.projectedEndpoint_hasFDerivAt_of_nonpos hq
      ⟨ht.1, le_of_not_ge hnonneg⟩

end LocalRegularControlledContinuousAutonomousSelector

end SymmetricEndpointDerivative

end Poincare
