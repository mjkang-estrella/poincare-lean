import Poincare.Global.RegularVariationalSelectorSymmetricEndpointDerivative
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint `C¹` regularity from one regular variational selector

The symmetric endpoint theorem gives the spatial partial derivative of the
projected selector.  Its ODE gives the time partial derivative.  Both partial
derivative fields are continuous because the retained augmented selector is
jointly continuous and the base field is locally `C¹` on the protected tube.
Mathlib's bivariate partial-derivative theorem therefore gives the full joint
Frechet derivative and hence local joint `C¹` regularity.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section JointC1

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [FiniteDimensional ℝ X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ q : X} {t : ℝ}

/-- Spatial partial derivative retained by the first variational selector. -/
def projectedSpatialDerivative
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (q : X) (t : ℝ) : X →L[ℝ] X :=
  (H.selector (q, ContinuousLinearMap.id ℝ X) t).2

/-- Time partial derivative of the projected selector, written as a
continuous linear map from the one-dimensional time space. -/
def projectedTimeDerivative
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (q : X) (t : ℝ) : ℝ →L[ℝ] X :=
  ContinuousLinearMap.toSpanSingleton ℝ
    (F (H.projectFirstVariational.selector q t))

/-- Full derivative in initial state and relative time. -/
def projectedJointDerivative
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (q : X) (t : ℝ) : (X × ℝ) →L[ℝ] X :=
  (H.projectedSpatialDerivative q t).coprod
    (H.projectedTimeDerivative q t)

private theorem identityTimeEmbedding_continuous :
    Continuous (fun v : X × ℝ ↦
      ((v.1, ContinuousLinearMap.id ℝ X), v.2)) :=
  (continuous_fst.prodMk continuous_const).prodMk continuous_snd

private theorem identityEmbedding_mem_ball
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ)) :
    (q, ContinuousLinearMap.id ℝ X) ∈
      ball (x₀, ContinuousLinearMap.id ℝ X)
        (H.initialRadius : ℝ) := by
  rw [Metric.mem_ball] at hq ⊢
  rw [Prod.dist_eq, dist_self,
    max_eq_left (dist_nonneg : 0 ≤ dist q x₀)]
  exact hq

private theorem augmentedSelector_continuousAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ContinuousAt
      (fun v : X × ℝ ↦
        H.selector (v.1, ContinuousLinearMap.id ℝ X) v.2)
      (q, t) := by
  have hqAug := identityEmbedding_mem_ball H hq
  have hspace : closedBall
      (x₀, ContinuousLinearMap.id ℝ X) (H.initialRadius : ℝ) ∈
      nhds (q, ContinuousLinearMap.id ℝ X) :=
    closedBall_mem_nhds_of_mem hqAug
  have htime : Icc (-H.epsilon) H.epsilon ∈ nhds t := by
    apply Icc_mem_nhds
    · linarith [ht.1, H.epsilon_pos]
    · linarith [ht.2, H.epsilon_pos]
  have hselector := H.selector_continuousOn.continuousAt
    (prod_mem_nhds hspace htime)
  have hembed : ContinuousAt
      (fun v : X × ℝ ↦
        ((v.1, ContinuousLinearMap.id ℝ X), v.2)) (q, t) :=
    (identityTimeEmbedding_continuous (X := X)).continuousAt
  have hcomp : ContinuousAt
      (fun v : X × ℝ ↦
        (Function.uncurry H.selector)
          ((v.1, ContinuousLinearMap.id ℝ X), v.2)) (q, t) :=
    ContinuousAt.comp' hselector hembed
  simpa only [Function.uncurry] using hcomp

/-- The spatial partial derivative field is continuous at every point in the
open protected product neighborhood. -/
theorem projectedSpatialDerivative_continuousAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ContinuousAt (Function.uncurry H.projectedSpatialDerivative) (q, t) := by
  simpa only [projectedSpatialDerivative, Function.uncurry] using
    (augmentedSelector_continuousAt H hq ht).snd

/-- The ODE time-partial derivative field is continuous on the same open
product neighborhood. -/
theorem projectedTimeDerivative_continuousAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ContinuousAt (Function.uncurry H.projectedTimeDerivative) (q, t) := by
  let B := H.projectFirstVariational
  have hqClosed : q ∈ closedBall x₀ (B.initialRadius : ℝ) := by
    exact ball_subset_closedBall hq
  have htClosed : t ∈ Icc (-(B.epsilon / 2)) (B.epsilon / 2) := by
    exact ⟨ht.1.le, ht.2.le⟩
  have htrajectoryProtected :=
    B.selector_mem_protectedInnerBall hqClosed htClosed
  have htrajectoryTube : B.selector q t ∈
      closedBall x₀ (B.tubeRadius : ℝ) := by
    rw [Metric.mem_closedBall] at htrajectoryProtected ⊢
    exact htrajectoryProtected.trans
      B.protectedInnerRadius_lt_tubeRadius.le
  have hfield : ContinuousAt F (B.selector q t) :=
    (B.field_contDiffAt_one _ htrajectoryTube).continuousAt
  have hbaseSelector : ContinuousAt
      (fun v : X × ℝ ↦ B.selector v.1 v.2) (q, t) := by
    simpa only [B, projectFirstVariational_selector] using
      (augmentedSelector_continuousAt H hq ht).fst
  have hfieldComp : ContinuousAt
      (fun v : X × ℝ ↦ F (B.selector v.1 v.2)) (q, t) :=
    ContinuousAt.comp' hfield hbaseSelector
  let S : X ≃L[ℝ] (ℝ →L[ℝ] X) :=
    ContinuousLinearMap.toSpanSingletonCLE
  have hspan : ContinuousAt
      (fun v : X × ℝ ↦ S (F (B.selector v.1 v.2))) (q, t) :=
    ContinuousAt.comp' S.continuousAt hfieldComp
  simpa [projectedTimeDerivative, Function.uncurry, B, S,
    ContinuousLinearMap.toSpanSingletonCLE] using hspan

/-- The complete space-time derivative field is continuous on the protected
product neighborhood. -/
theorem projectedJointDerivative_continuousAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ContinuousAt (Function.uncurry H.projectedJointDerivative) (q, t) := by
  have hpair := (H.projectedSpatialDerivative_continuousAt hq ht).prodMk
    (H.projectedTimeDerivative_continuousAt hq ht)
  let C :
      ((X →L[ℝ] X) × (ℝ →L[ℝ] X)) ≃L[ℝ]
        ((X × ℝ) →L[ℝ] X) :=
    ContinuousLinearMap.coprodEquivL ℝ
  have hcoprod : ContinuousAt
      (fun v : X × ℝ ↦ C
        (H.projectedSpatialDerivative v.1 v.2,
          H.projectedTimeDerivative v.1 v.2)) (q, t) :=
    ContinuousAt.comp' C.continuousAt hpair
  simpa [projectedJointDerivative, Function.uncurry, C,
    ContinuousLinearMap.coprodEquivL] using hcoprod

/-- On the open protected half interval, the uncurried projected selector
has the expected strict joint Frechet derivative. -/
theorem projectedUncurriedSelector_hasStrictFDerivAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    HasStrictFDerivAt
      (Function.uncurry H.projectFirstVariational.selector)
      (H.projectedJointDerivative q t) (q, t) := by
  let U : Set (X × ℝ) :=
    ball x₀ (H.initialRadius : ℝ) ×ˢ
      Ioo (-(H.epsilon / 2)) (H.epsilon / 2)
  have hU : U ∈ nhds (q, t) :=
    prod_mem_nhds
      (isOpen_ball.mem_nhds hq)
      (isOpen_Ioo.mem_nhds ht)
  have hspatial : ∀ᶠ v in nhds (q, t),
      HasFDerivAt
        (H.projectFirstVariational.selector · v.2)
        (H.projectedSpatialDerivative v.1 v.2) v.1 := by
    filter_upwards [hU] with v hv
    exact H.projectedEndpoint_hasFDerivAt_symmetric hv.1
      ⟨hv.2.1.le, hv.2.2.le⟩
  have htime : ∀ᶠ v in nhds (q, t),
      HasFDerivAt
        (H.projectFirstVariational.selector v.1)
        (H.projectedTimeDerivative v.1 v.2) v.2 := by
    filter_upwards [hU] with v hv
    let B := H.projectFirstVariational
    have hvClosed : v.1 ∈ closedBall x₀ (B.initialRadius : ℝ) :=
      ball_subset_closedBall hv.1
    have hvTimeClosed : v.2 ∈ Icc (-B.epsilon) B.epsilon := by
      change v.2 ∈ Icc (-H.epsilon) H.epsilon
      constructor <;> linarith [hv.2.1, hv.2.2, H.epsilon_pos]
    have hvTimeOpen : v.2 ∈ Ioo (-B.epsilon) B.epsilon := by
      change v.2 ∈ Ioo (-H.epsilon) H.epsilon
      constructor <;> linarith [hv.2.1, hv.2.2, H.epsilon_pos]
    have hwithin := (B.selector_data v.1 hvClosed).2.1
      v.2 hvTimeClosed
    have hat := hwithin.hasDerivAt
      (Icc_mem_nhds hvTimeOpen.1 hvTimeOpen.2)
    simpa only [B, projectedTimeDerivative] using hat.hasFDerivAt
  have hstrict := hasStrictFDerivAt_uncurry_coprod
    (u := (q, t))
    (f := H.projectFirstVariational.selector)
    (f₁ := H.projectedSpatialDerivative)
    (f₂ := H.projectedTimeDerivative)
    hspatial htime
    (H.projectedSpatialDerivative_continuousAt hq ht)
    (H.projectedTimeDerivative_continuousAt hq ht)
  simpa only [projectedJointDerivative] using hstrict

/-- The retained one-level variational selector supplies complete local
first-order data for the uncurried base selector at every nearby initial
state and every protected interior time, including negative restart times. -/
def projectedUncurriedSelector_firstOrderDataAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    LocalFirstOrderVariationalData
      (Function.uncurry H.projectFirstVariational.selector) (q, t) where
  D₁ := Function.uncurry H.projectedJointDerivative
  hasFDerivAt_eventually := by
    let U : Set (X × ℝ) :=
      ball x₀ (H.initialRadius : ℝ) ×ˢ
        Ioo (-(H.epsilon / 2)) (H.epsilon / 2)
    refine ⟨U, ?_, ?_⟩
    · exact prod_mem_nhds
        (isOpen_ball.mem_nhds hq)
        (isOpen_Ioo.mem_nhds ht)
    · intro v hv
      exact (H.projectedUncurriedSelector_hasStrictFDerivAt
        hv.1 hv.2).hasFDerivAt
  D₁_contDiffAt_zero := by
    let U : Set (X × ℝ) :=
      ball x₀ (H.initialRadius : ℝ) ×ˢ
        Ioo (-(H.epsilon / 2)) (H.epsilon / 2)
    apply contDiffAt_zero.2
    refine ⟨U, ?_, ?_⟩
    · exact prod_mem_nhds
        (isOpen_ball.mem_nhds hq)
        (isOpen_Ioo.mem_nhds ht)
    · intro v hv
      exact (H.projectedJointDerivative_continuousAt hv.1 hv.2).continuousWithinAt

/-- Central-state compatibility form of the local first-order data. -/
def projectedUncurriedSelector_firstOrderData
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    LocalFirstOrderVariationalData
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t) :=
  H.projectedUncurriedSelector_firstOrderDataAt
    (mem_ball_self (by exact_mod_cast H.initialRadius_pos)) ht

/-- Joint `C¹` regularity of the projected selector, valid at negative as
well as positive protected interior times. -/
theorem projectedUncurriedSelector_contDiffAt_one
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ContDiffAt ℝ 1
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t) :=
  (H.projectedUncurriedSelector_firstOrderData ht).contDiffAt_one

end LocalRegularControlledContinuousAutonomousSelector

end JointC1

end Poincare
