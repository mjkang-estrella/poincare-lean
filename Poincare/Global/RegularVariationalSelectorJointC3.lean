import Poincare.Global.RegularVariationalSelectorJointC1

/-!
# Joint `C³` regularity from a coherent variational hierarchy

The one-level joint theorem identifies the derivative of a projected
selector as the coproduct of its retained spatial variation and its ODE time
derivative.  A coherent next variational selector makes the augmented
selector jointly `C¹`, hence makes that derivative field `C¹` and the base
selector `C²`.  Repeating at the next level makes the spatial derivative
field `C²`; local `C²` regularity of the base vector field along the endpoint
then closes joint `C³` regularity of the exact retained base selector.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section GenericJointBootstrap

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [FiniteDimensional ℝ X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ : X} {t : ℝ}

private theorem endpoint_mem_tube
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (ht : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    H.projectFirstVariational.selector x₀ t ∈
      closedBall x₀ (H.projectFirstVariational.tubeRadius : ℝ) := by
  let B := H.projectFirstVariational
  have hx : x₀ ∈ closedBall x₀ (B.initialRadius : ℝ) :=
    mem_closedBall_self (by positivity)
  have hprotected := B.selector_mem_protectedInnerBall hx
    (show t ∈ Icc (-(B.epsilon / 2)) (B.epsilon / 2) by
      exact ⟨ht.1.le, ht.2.le⟩)
  rw [Metric.mem_closedBall] at hprotected ⊢
  exact hprotected.trans B.protectedInnerRadius_lt_tubeRadius.le

/-- A coherent next variational selector upgrades the projected selector
from joint `C¹` to joint `C²`. -/
theorem projectedUncurriedSelector_contDiffAt_two_of_next
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (K : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (firstVariationalAugmentedField F))
      ((x₀, ContinuousLinearMap.id ℝ X),
        ContinuousLinearMap.id ℝ (FirstVariationalState X)))
    (hselector : K.projectFirstVariational.selector = H.selector)
    (htH : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2))
    (htK : t ∈ Ioo (-(K.epsilon / 2)) (K.epsilon / 2)) :
    ContDiffAt ℝ 2
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t) := by
  have hAugRaw := K.projectedUncurriedSelector_contDiffAt_one htK
  have hAug : ContDiffAt ℝ 1 (Function.uncurry H.selector)
      ((x₀, ContinuousLinearMap.id ℝ X), t) := by
    rw [hselector] at hAugRaw
    exact hAugRaw
  let embed : X × ℝ → FirstVariationalState X × ℝ :=
    fun v ↦ ((v.1, ContinuousLinearMap.id ℝ X), v.2)
  have hembed : ContDiffAt ℝ 1 embed (x₀, t) :=
    (contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd
  have hAFull := hAug.comp (x₀, t) hembed
  have hA : ContDiffAt ℝ 1
      (Function.uncurry H.projectedSpatialDerivative) (x₀, t) := by
    simpa only [embed, projectedSpatialDerivative, Function.uncurry] using
      hAFull.snd
  have hbeta : ContDiffAt ℝ 1
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t) :=
    H.projectedUncurriedSelector_contDiffAt_one htH
  have hfield : ContDiffAt ℝ 1 F
      (H.projectFirstVariational.selector x₀ t) :=
    H.projectFirstVariational.field_contDiffAt_one _
      (H.endpoint_mem_tube htH)
  have hfieldComp : ContDiffAt ℝ 1
      (fun v : X × ℝ ↦
        F (H.projectFirstVariational.selector v.1 v.2)) (x₀, t) :=
    hfield.comp (x₀, t) hbeta
  let S : X ≃L[ℝ] (ℝ →L[ℝ] X) :=
    ContinuousLinearMap.toSpanSingletonCLE
  have hTimeRaw : ContDiffAt ℝ 1
      (fun v : X × ℝ ↦ S
        (F (H.projectFirstVariational.selector v.1 v.2))) (x₀, t) :=
    S.contDiff.contDiffAt.comp (x₀, t) hfieldComp
  have hTime : ContDiffAt ℝ 1
      (Function.uncurry H.projectedTimeDerivative) (x₀, t) := by
    simpa [S, projectedTimeDerivative, Function.uncurry,
      ContinuousLinearMap.toSpanSingletonCLE] using hTimeRaw
  let C :
      ((X →L[ℝ] X) × (ℝ →L[ℝ] X)) ≃L[ℝ]
        ((X × ℝ) →L[ℝ] X) :=
    ContinuousLinearMap.coprodEquivL ℝ
  have hDRaw : ContDiffAt ℝ 1
      (fun v : X × ℝ ↦ C
        (H.projectedSpatialDerivative v.1 v.2,
          H.projectedTimeDerivative v.1 v.2)) (x₀, t) :=
    C.contDiff.contDiffAt.comp (x₀, t) (hA.prodMk hTime)
  have hD : ContDiffAt ℝ 1
      (Function.uncurry H.projectedJointDerivative) (x₀, t) := by
    simpa [C, projectedJointDerivative, Function.uncurry,
      ContinuousLinearMap.coprodEquivL] using hDRaw
  have hder : ∃ U ∈ nhds (x₀, t), ∀ q ∈ U,
      HasFDerivAt
        (Function.uncurry H.projectFirstVariational.selector)
        (Function.uncurry H.projectedJointDerivative q) q := by
    let U : Set (X × ℝ) :=
      ball x₀ (H.initialRadius : ℝ) ×ˢ
        Ioo (-(H.epsilon / 2)) (H.epsilon / 2)
    refine ⟨U, ?_, ?_⟩
    · exact prod_mem_nhds
        (ball_mem_nhds x₀ (by exact_mod_cast H.initialRadius_pos))
        (isOpen_Ioo.mem_nhds htH)
    · intro q hq
      exact (H.projectedUncurriedSelector_hasStrictFDerivAt
        hq.1 hq.2).hasFDerivAt
  exact
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
      (f := Function.uncurry H.projectFirstVariational.selector)
      (x := (x₀, t))).2
      ⟨Function.uncurry H.projectedJointDerivative,
        hder, hD⟩

/-- If the augmented selector and the projected base selector are already
jointly `C²`, and the base field is `C²` at the selected endpoint, then the
same retained derivative formula upgrades the projected selector to joint
`C³`. -/
theorem projectedUncurriedSelector_contDiffAt_three_of_augmented_two
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (htH : t ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2))
    (hAug : ContDiffAt ℝ 2 (Function.uncurry H.selector)
      ((x₀, ContinuousLinearMap.id ℝ X), t))
    (hbeta : ContDiffAt ℝ 2
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t))
    (hfield : ContDiffAt ℝ 2 F
      (H.projectFirstVariational.selector x₀ t)) :
    ContDiffAt ℝ 3
      (Function.uncurry H.projectFirstVariational.selector) (x₀, t) := by
  let embed : X × ℝ → FirstVariationalState X × ℝ :=
    fun v ↦ ((v.1, ContinuousLinearMap.id ℝ X), v.2)
  have hembed : ContDiffAt ℝ 2 embed (x₀, t) :=
    (contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd
  have hAFull := hAug.comp (x₀, t) hembed
  have hA : ContDiffAt ℝ 2
      (Function.uncurry H.projectedSpatialDerivative) (x₀, t) := by
    simpa only [embed, projectedSpatialDerivative, Function.uncurry] using
      hAFull.snd
  have hfieldComp : ContDiffAt ℝ 2
      (fun v : X × ℝ ↦
        F (H.projectFirstVariational.selector v.1 v.2)) (x₀, t) :=
    hfield.comp (x₀, t) hbeta
  let S : X ≃L[ℝ] (ℝ →L[ℝ] X) :=
    ContinuousLinearMap.toSpanSingletonCLE
  have hTimeRaw : ContDiffAt ℝ 2
      (fun v : X × ℝ ↦ S
        (F (H.projectFirstVariational.selector v.1 v.2))) (x₀, t) :=
    S.contDiff.contDiffAt.comp (x₀, t) hfieldComp
  have hTime : ContDiffAt ℝ 2
      (Function.uncurry H.projectedTimeDerivative) (x₀, t) := by
    simpa [S, projectedTimeDerivative, Function.uncurry,
      ContinuousLinearMap.toSpanSingletonCLE] using hTimeRaw
  let C :
      ((X →L[ℝ] X) × (ℝ →L[ℝ] X)) ≃L[ℝ]
        ((X × ℝ) →L[ℝ] X) :=
    ContinuousLinearMap.coprodEquivL ℝ
  have hDRaw : ContDiffAt ℝ 2
      (fun v : X × ℝ ↦ C
        (H.projectedSpatialDerivative v.1 v.2,
          H.projectedTimeDerivative v.1 v.2)) (x₀, t) :=
    C.contDiff.contDiffAt.comp (x₀, t) (hA.prodMk hTime)
  have hD : ContDiffAt ℝ 2
      (Function.uncurry H.projectedJointDerivative) (x₀, t) := by
    simpa [C, projectedJointDerivative, Function.uncurry,
      ContinuousLinearMap.coprodEquivL] using hDRaw
  have hder : ∃ U ∈ nhds (x₀, t), ∀ q ∈ U,
      HasFDerivAt
        (Function.uncurry H.projectFirstVariational.selector)
        (Function.uncurry H.projectedJointDerivative q) q := by
    let U : Set (X × ℝ) :=
      ball x₀ (H.initialRadius : ℝ) ×ˢ
        Ioo (-(H.epsilon / 2)) (H.epsilon / 2)
    refine ⟨U, ?_, ?_⟩
    · exact prod_mem_nhds
        (ball_mem_nhds x₀ (by exact_mod_cast H.initialRadius_pos))
        (isOpen_Ioo.mem_nhds htH)
    · intro q hq
      exact (H.projectedUncurriedSelector_hasStrictFDerivAt
        hq.1 hq.2).hasFDerivAt
  exact
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 2)
      (f := Function.uncurry H.projectFirstVariational.selector)
      (x := (x₀, t))).2
      ⟨Function.uncurry H.projectedJointDerivative,
        hder, hD⟩

end LocalRegularControlledContinuousAutonomousSelector

end GenericJointBootstrap

section JointTowerAssembly

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Any local joint `C³` proof yields the explicit three-level derivative
tower consumed by the point-flow package boundary. -/
theorem LocalThirdOrderVariationalTower.nonempty_ofContDiffAtThree
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 3 f x) :
    Nonempty (LocalThirdOrderVariationalTower f x) := by
  rcases
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 2)
        (f := f) (x := x)).1 hf with
    ⟨D₁, hD₁, hD₁C2⟩
  rcases
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)
        (f := D₁) (x := x)).1 hD₁C2 with
    ⟨D₂, hD₂, hD₂C1⟩
  rcases
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)
        (f := D₂) (x := x)).1 hD₂C1 with
    ⟨D₃, hD₃, hD₃C0⟩
  exact ⟨
    { D₁ := D₁
      D₂ := D₂
      D₃ := D₃
      f_hasFDerivAt_eventually := hD₁
      D₁_hasFDerivAt_eventually := hD₂
      D₂_hasFDerivAt_eventually := hD₃
      D₃_contDiffAt_zero := hD₃C0 }⟩

/-- Choice form of `nonempty_ofContDiffAtThree`. -/
def LocalThirdOrderVariationalTower.ofContDiffAtThree
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 3 f x) :
    LocalThirdOrderVariationalTower f x :=
  Classical.choice
    (LocalThirdOrderVariationalTower.nonempty_ofContDiffAtThree hf)

variable [FiniteDimensional ℝ X]

namespace RegularCoherentThreeLevelVariationalSelectorTower

variable {F : X → X} {x : X} {t : ℝ}

/-- The first two levels make the exact retained base selector jointly
`C²`. -/
theorem baseUncurriedSelector_contDiffAt_two
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    (ht : t ∈ Ioo (-(T.base.epsilon / 2)) (T.base.epsilon / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry T.base.selector) (x, t) := by
  have htFirst : t ∈ Ioo (-(T.first.epsilon / 2))
      (T.first.epsilon / 2) := by
    simpa only [base] using ht
  have htSecond : t ∈ Ioo (-(T.second.epsilon / 2))
      (T.second.epsilon / 2) := by
    simpa only [base, first] using ht
  have h := T.first.projectedUncurriedSelector_contDiffAt_two_of_next
    T.second (by rfl) htFirst htSecond
  simpa only [base] using h

/-- The second and third levels make the retained first-variational selector
jointly `C²`. -/
theorem firstUncurriedSelector_contDiffAt_two
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    (ht : t ∈ Ioo (-(T.base.epsilon / 2)) (T.base.epsilon / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry T.first.selector)
      (coherentFirstCenter x, t) := by
  have htSecond : t ∈ Ioo (-(T.second.epsilon / 2))
      (T.second.epsilon / 2) := by
    simpa only [base, first] using ht
  have htThird : t ∈ Ioo (-(T.third.epsilon / 2))
      (T.third.epsilon / 2) := by
    simpa only [base, first, second] using ht
  have h := T.second.projectedUncurriedSelector_contDiffAt_two_of_next
    T.third (by rfl) htSecond htThird
  simpa only [first] using h

/-- All three coherent levels assemble genuine joint `C³` regularity of the
exact retained base selector.  Only local `C²` regularity of the base field
at the selected endpoint is additionally needed for the ODE time column. -/
theorem baseUncurriedSelector_contDiffAt_three
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    (ht : t ∈ Ioo (-(T.base.epsilon / 2)) (T.base.epsilon / 2))
    (hfield : ContDiffAt ℝ 2 F (T.base.selector x t)) :
    ContDiffAt ℝ 3 (Function.uncurry T.base.selector) (x, t) := by
  have htFirst : t ∈ Ioo (-(T.first.epsilon / 2))
      (T.first.epsilon / 2) := by
    simpa only [base] using ht
  have hbeta := T.baseUncurriedSelector_contDiffAt_two ht
  have hAug := T.firstUncurriedSelector_contDiffAt_two ht
  have h := T.first.projectedUncurriedSelector_contDiffAt_three_of_augmented_two
    htFirst hAug hbeta hfield
  simpa only [base] using h

/-- Explicit forward joint third-order tower for the exact retained base
selector. -/
def baseUncurriedSelector_thirdOrderTower
    (T : RegularCoherentThreeLevelVariationalSelectorTower F x)
    (ht : t ∈ Ioo (-(T.base.epsilon / 2)) (T.base.epsilon / 2))
    (hfield : ContDiffAt ℝ 2 F (T.base.selector x t)) :
    LocalThirdOrderVariationalTower
      (Function.uncurry T.base.selector) (x, t) :=
  LocalThirdOrderVariationalTower.ofContDiffAtThree
    (T.baseUncurriedSelector_contDiffAt_three ht hfield)

end RegularCoherentThreeLevelVariationalSelectorTower

end JointTowerAssembly

end Poincare
