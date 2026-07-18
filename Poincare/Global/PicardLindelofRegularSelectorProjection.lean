import Poincare.Global.PicardLindelofRegularControlledSelector

/-!
# Coherent projection of a regular variational selector

A selector for the first variational augmentation of `F` contains a selector
for `F` in its first component.  Fixing the initial operator to the identity
and projecting preserves every piece of the regular controlled package:
initial values, ODE, tube membership, joint continuity, Lipschitz control,
the speed bound, strict margin, and local `C¹` regularity.  Iterating this
single construction produces a coherent variational tower.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section Projection

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ : X}

/-- Embedding with a fixed identity operator preserves distance from the
corresponding augmented centre. -/
private theorem identity_embedding_mem_closedBall
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    {x : X}
    (hx : x ∈ closedBall x₀ (H.initialRadius : ℝ)) :
    (x, ContinuousLinearMap.id ℝ X) ∈
      closedBall (x₀, ContinuousLinearMap.id ℝ X)
        (H.initialRadius : ℝ) := by
  rw [Metric.mem_closedBall] at hx ⊢
  rw [Prod.dist_eq, dist_self]
  rw [max_eq_left (dist_nonneg : 0 ≤ dist x x₀)]
  exact hx

/-- The analogous embedding fact for the outer tube. -/
private theorem identity_embedding_mem_tube
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    {x : X}
    (hx : x ∈ closedBall x₀ (H.tubeRadius : ℝ)) :
    (x, ContinuousLinearMap.id ℝ X) ∈
      closedBall (x₀, ContinuousLinearMap.id ℝ X)
        (H.tubeRadius : ℝ) := by
  rw [Metric.mem_closedBall] at hx ⊢
  rw [Prod.dist_eq, dist_self]
  rw [max_eq_left (dist_nonneg : 0 ≤ dist x x₀)]
  exact hx

/-- Project one regular first-variational selector to a regular selector for
its base field.  The output selector is definitionally the first component
of the input selector at identity initial variation. -/
def projectFirstVariational
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X)) :
    LocalRegularControlledContinuousAutonomousSelector F x₀ where
  epsilon := H.epsilon
  epsilon_pos := H.epsilon_pos
  tubeRadius := H.tubeRadius
  initialRadius := H.initialRadius
  speedBound := H.speedBound
  lipschitzConstant := H.lipschitzConstant
  initialRadius_pos := H.initialRadius_pos
  selector := fun x t ↦
    (H.selector (x, ContinuousLinearMap.id ℝ X) t).1
  field_lipschitzOn := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' := identity_embedding_mem_tube H hx
    have hy' := identity_embedding_mem_tube H hy
    have hfull := H.field_lipschitzOn.dist_le_mul
      (x, ContinuousLinearMap.id ℝ X) hx'
      (y, ContinuousLinearMap.id ℝ X) hy'
    calc
      dist (F x) (F y) ≤
          dist
            (firstVariationalAugmentedField F
              (x, ContinuousLinearMap.id ℝ X))
            (firstVariationalAugmentedField F
              (y, ContinuousLinearMap.id ℝ X)) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ ≤ (H.lipschitzConstant : ℝ) *
          dist (x, ContinuousLinearMap.id ℝ X)
            (y, ContinuousLinearMap.id ℝ X) := hfull
      _ = (H.lipschitzConstant : ℝ) * dist x y := by
        rw [Prod.dist_eq, dist_self,
          max_eq_left (dist_nonneg : 0 ≤ dist x y)]
  selector_data := by
    intro x hx
    have hdata := H.selector_data
      (x, ContinuousLinearMap.id ℝ X)
      (identity_embedding_mem_closedBall H hx)
    refine ⟨congrArg Prod.fst hdata.1, ?_, ?_⟩
    · intro t ht
      have hfst :=
        (hdata.2.1 t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
      convert hfst using 1 <;>
        simp [firstVariationalAugmentedField]
    · intro t ht
      have hmem := hdata.2.2 t ht
      rw [Metric.mem_closedBall, Prod.dist_eq] at hmem
      rw [Metric.mem_closedBall]
      exact (le_max_left _ _).trans hmem
  selector_continuousOn := by
    let embed : X × ℝ → (X × (X →L[ℝ] X)) × ℝ :=
      fun q ↦ ((q.1, ContinuousLinearMap.id ℝ X), q.2)
    have hembed : Continuous embed :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    have hmap : MapsTo embed
        (closedBall x₀ (H.initialRadius : ℝ) ×ˢ
          Icc (-H.epsilon) H.epsilon)
        (closedBall (x₀, ContinuousLinearMap.id ℝ X)
            (H.initialRadius : ℝ) ×ˢ Icc (-H.epsilon) H.epsilon) := by
      intro q hq
      exact ⟨identity_embedding_mem_closedBall H hq.1, hq.2⟩
    have hcomp := H.selector_continuousOn.comp hembed.continuousOn hmap
    simpa only [Function.uncurry, embed] using hcomp.fst
  initialRadius_lt_tubeRadius := H.initialRadius_lt_tubeRadius
  field_norm_le := by
    intro x hx
    have hfull := H.field_norm_le
      (x, ContinuousLinearMap.id ℝ X)
      (identity_embedding_mem_tube H hx)
    rw [firstVariationalAugmentedField, Prod.norm_def] at hfull
    exact (le_max_left _ _).trans hfull
  speed_time_le_margin := H.speed_time_le_margin
  field_contDiffAt_one := by
    intro x hx
    have htop := H.field_contDiffAt_one
      (x, ContinuousLinearMap.id ℝ X)
      (identity_embedding_mem_tube H hx)
    have hembed : ContDiffAt ℝ 1
        (fun y : X ↦ (y, ContinuousLinearMap.id ℝ X)) x :=
      contDiffAt_id.prodMk contDiffAt_const
    have hcomp := htop.comp x hembed
    simpa only [firstVariationalAugmentedField] using hcomp.fst

@[simp] theorem projectFirstVariational_selector
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (x : X) (t : ℝ) :
    H.projectFirstVariational.selector x t =
      (H.selector (x, ContinuousLinearMap.id ℝ X) t).1 := rfl

end LocalRegularControlledContinuousAutonomousSelector

end Projection

end Poincare
