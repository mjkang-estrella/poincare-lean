import Poincare.Global.PicardLindelofRegularControlledSelector

/-!
# Time reversal of a regular autonomous selector

A selector for `F` on a symmetric interval gives, by precomposition with
`t ↦ -t`, a selector for `-F` with exactly the same radii, bounds, and local
regularity.  Keeping this construction definitionally tied to the original
selector is useful for backward endpoint differentiability at a restart.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section RegularSelectorTimeReversal

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ : X}

private theorem firstVariationalAugmentedField_neg_eq :
    firstVariationalAugmentedField (fun x : X ↦ -F x) =
      fun z ↦ -(firstVariationalAugmentedField F z) := by
  funext z
  simp only [firstVariationalAugmentedField, fderiv_fun_neg,
    ContinuousLinearMap.neg_comp, Prod.neg_mk]

/-- Reverse the relative-time parameter of a regular autonomous selector.
The result solves the negated autonomous field and retains all quantitative
data unchanged. -/
def reverseTime
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀) :
    LocalRegularControlledContinuousAutonomousSelector
      (fun x ↦ -F x) x₀ where
  epsilon := H.epsilon
  epsilon_pos := H.epsilon_pos
  tubeRadius := H.tubeRadius
  initialRadius := H.initialRadius
  speedBound := H.speedBound
  lipschitzConstant := H.lipschitzConstant
  initialRadius_pos := H.initialRadius_pos
  selector := fun x t ↦ H.selector x (-t)
  field_lipschitzOn := H.field_lipschitzOn.neg
  selector_data := by
    intro x hx
    have hdata := H.selector_data x hx
    refine ⟨by simpa using hdata.1, ?_, ?_⟩
    · intro t ht
      have hneg : -t ∈ Icc (-H.epsilon) H.epsilon := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hmaps : MapsTo (fun s : ℝ ↦ -s)
          (Icc (-H.epsilon) H.epsilon)
          (Icc (-H.epsilon) H.epsilon) := by
        intro s hs
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hcomp := (hdata.2.1 (-t) hneg).scomp t
        (hasDerivAt_neg t).hasDerivWithinAt hmaps
      simpa only [Function.comp_def, neg_smul, one_smul] using hcomp
    · intro t ht
      have hneg : -t ∈ Icc (-H.epsilon) H.epsilon := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hdata.2.2 (-t) hneg
  selector_continuousOn := by
    let reverse : X × ℝ → X × ℝ := fun q ↦ (q.1, -q.2)
    have hreverse : Continuous reverse :=
      continuous_fst.prodMk continuous_snd.neg
    have hmaps : MapsTo reverse
        (closedBall x₀ (H.initialRadius : ℝ) ×ˢ
          Icc (-H.epsilon) H.epsilon)
        (closedBall x₀ (H.initialRadius : ℝ) ×ˢ
          Icc (-H.epsilon) H.epsilon) := by
      intro q hq
      exact ⟨hq.1, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩⟩
    have hcomp := H.selector_continuousOn.comp
      hreverse.continuousOn hmaps
    simpa only [Function.uncurry, reverse] using hcomp
  initialRadius_lt_tubeRadius := H.initialRadius_lt_tubeRadius
  field_norm_le := by
    intro x hx
    simpa only [norm_neg] using H.field_norm_le x hx
  speed_time_le_margin := H.speed_time_le_margin
  field_contDiffAt_one := by
    intro x hx
    exact (H.field_contDiffAt_one x hx).neg

@[simp] theorem reverseTime_selector
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀)
    (x : X) (t : ℝ) :
    H.reverseTime.selector x t = H.selector x (-t) := rfl

/-- Time reversal specialized to a first variational augmentation.  This
version is built directly, rather than transported across an equality of
fields, so all quantitative projections and the selector itself reduce
definitionally to those of `H`. -/
def reverseTimeFirstVariational
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X)) :
    LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fun x : X ↦ -F x))
      (x₀, ContinuousLinearMap.id ℝ X) where
  epsilon := H.epsilon
  epsilon_pos := H.epsilon_pos
  tubeRadius := H.tubeRadius
  initialRadius := H.initialRadius
  speedBound := H.speedBound
  lipschitzConstant := H.lipschitzConstant
  initialRadius_pos := H.initialRadius_pos
  selector := fun x t ↦ H.selector x (-t)
  field_lipschitzOn := by
    rw [firstVariationalAugmentedField_neg_eq]
    exact H.field_lipschitzOn.neg
  selector_data := by
    intro x hx
    have hdata := H.selector_data x hx
    refine ⟨by simpa using hdata.1, ?_, ?_⟩
    · intro t ht
      have hneg : -t ∈ Icc (-H.epsilon) H.epsilon := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hmaps : MapsTo (fun s : ℝ ↦ -s)
          (Icc (-H.epsilon) H.epsilon)
          (Icc (-H.epsilon) H.epsilon) := by
        intro s hs
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hcomp := (hdata.2.1 (-t) hneg).scomp t
        (hasDerivAt_neg t).hasDerivWithinAt hmaps
      simpa only [Function.comp_def, neg_smul, one_smul,
        firstVariationalAugmentedField, fderiv_fun_neg,
        ContinuousLinearMap.neg_comp, Prod.neg_mk] using hcomp
    · intro t ht
      have hneg : -t ∈ Icc (-H.epsilon) H.epsilon := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hdata.2.2 (-t) hneg
  selector_continuousOn := by
    let reverse : (X × (X →L[ℝ] X)) × ℝ →
        (X × (X →L[ℝ] X)) × ℝ := fun q ↦ (q.1, -q.2)
    have hreverse : Continuous reverse :=
      continuous_fst.prodMk continuous_snd.neg
    have hmaps : MapsTo reverse
        (closedBall (x₀, ContinuousLinearMap.id ℝ X)
            (H.initialRadius : ℝ) ×ˢ Icc (-H.epsilon) H.epsilon)
        (closedBall (x₀, ContinuousLinearMap.id ℝ X)
            (H.initialRadius : ℝ) ×ˢ Icc (-H.epsilon) H.epsilon) := by
      intro q hq
      exact ⟨hq.1, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩⟩
    have hcomp := H.selector_continuousOn.comp
      hreverse.continuousOn hmaps
    simpa only [Function.uncurry, reverse] using hcomp
  initialRadius_lt_tubeRadius := H.initialRadius_lt_tubeRadius
  field_norm_le := by
    intro x hx
    simpa only [firstVariationalAugmentedField, fderiv_fun_neg,
      ContinuousLinearMap.neg_comp, Prod.neg_mk, Pi.neg_apply,
      Prod.norm_def, norm_neg] using
      H.field_norm_le x hx
  speed_time_le_margin := H.speed_time_le_margin
  field_contDiffAt_one := by
    intro x hx
    rw [firstVariationalAugmentedField_neg_eq]
    exact (H.field_contDiffAt_one x hx).neg

@[simp] theorem reverseTimeFirstVariational_selector
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (x : X × (X →L[ℝ] X)) (t : ℝ) :
    H.reverseTimeFirstVariational.selector x t = H.selector x (-t) := rfl

end LocalRegularControlledContinuousAutonomousSelector

end RegularSelectorTimeReversal

end Poincare
