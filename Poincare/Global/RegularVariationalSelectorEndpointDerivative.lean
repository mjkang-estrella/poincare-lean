import Poincare.Global.PointFlowRegularCoherentVariationalSelectorTower
import Poincare.Global.ParameterizedFlowDerivativeNestedBalls

/-!
# Endpoint derivative from one regular variational selector

This is the reusable residual step.  A regular selector for
`firstVariationalAugmentedField F` projects to a coherent selector for `F`.
On the protected half interval, the retained operator component is the
Frechet derivative of the projected endpoint map.  Iterating the theorem at
the first, second, and third augmented levels supplies the three endpoint
identifications required by the smooth-dependence tower.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section OneVariationalLevel

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ q : X} {t : ℝ}

/-- On the protected positive half interval, the operator component of a
regular first-variational selector is the endpoint Frechet derivative of its
projected base selector. -/
theorem projectedEndpoint_hasFDerivAt
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField F)
      (x₀, ContinuousLinearMap.id ℝ X))
    (hq : q ∈ ball x₀ (H.initialRadius : ℝ))
    (ht : t ∈ Icc (0 : ℝ) (H.epsilon / 2)) :
    HasFDerivAt (fun y : X ↦ H.projectFirstVariational.selector y t)
      (H.selector (q, ContinuousLinearMap.id ℝ X) t).2 q := by
  let B := H.projectFirstVariational
  let T : ℝ := H.epsilon / 2
  let Psi : X → ℝ → X := fun h tau ↦
    (H.selector (q, ContinuousLinearMap.id ℝ X) tau).2 h
  let D : X →L[ℝ] X :=
    (H.selector (q, ContinuousLinearMap.id ℝ X) t).2
  have hT : 0 < T := by
    dsimp only [T]
    linarith [H.epsilon_pos]
  have hqClosed : q ∈ closedBall x₀ (B.initialRadius : ℝ) := by
    exact ball_subset_closedBall hq
  have htimeSubset : Icc (0 : ℝ) T ⊆ Icc (-H.epsilon) H.epsilon := by
    intro tau htau
    rcases htau with ⟨htau0, htauT⟩
    dsimp only [T] at htauT
    constructor <;> linarith [H.epsilon_pos]
  have htimeProtected :
      Icc (0 : ℝ) T ⊆ Icc (-(B.epsilon / 2)) (B.epsilon / 2) := by
    intro tau htau
    change tau ∈ Icc (-(H.epsilon / 2)) (H.epsilon / 2)
    rcases htau with ⟨htau0, htauT⟩
    dsimp only [T] at htauT
    constructor <;> linarith [H.epsilon_pos]
  have hbaseData := B.selector_data q hqClosed
  have hbaseDer : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (B.selector q) (F (B.selector q tau))
        (Icc (0 : ℝ) T) tau := by
    intro tau htau
    exact (hbaseData.2.1 tau (htimeSubset htau)).mono htimeSubset
  have hbaseMem : ∀ tau ∈ Icc (0 : ℝ) T,
      B.selector q tau ∈ closedBall x₀ B.protectedInnerRadius := by
    intro tau htau
    exact B.selector_mem_protectedInnerBall hqClosed
      (htimeProtected htau)
  have hpert : ∀ᶠ h in nhds (0 : X),
      B.selector (q + h) 0 = B.selector q 0 +
          ContinuousLinearMap.id ℝ X h ∧
        (∀ tau ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (B.selector (q + h))
            (F (B.selector (q + h) tau)) (Icc (0 : ℝ) T) tau) ∧
        ∀ tau ∈ Icc (0 : ℝ) T,
          B.selector (q + h) tau ∈
            closedBall x₀ B.protectedInnerRadius := by
    have hballNhd : closedBall x₀ (B.initialRadius : ℝ) ∈ nhds q :=
      closedBall_mem_nhds_of_mem hq
    have htend : Tendsto (fun h : X ↦ q + h) (nhds 0) (nhds q) := by
      have hconst : Tendsto (fun _ : X ↦ q) (nhds 0) (nhds q) :=
        tendsto_const_nhds
      have hid : Tendsto (fun h : X ↦ h) (nhds 0) (nhds 0) :=
        tendsto_id
      simpa only [add_zero] using hconst.add hid
    filter_upwards [htend hballNhd] with h hh
    have hdata := B.selector_data (q + h) hh
    refine ⟨?_, ?_, ?_⟩
    · simp only [hdata.1, hbaseData.1, ContinuousLinearMap.id_apply]
    · intro tau htau
      exact (hdata.2.1 tau (htimeSubset htau)).mono htimeSubset
    · intro tau htau
      exact B.selector_mem_protectedInnerBall hh (htimeProtected htau)
  have hqAug :
      (q, ContinuousLinearMap.id ℝ X) ∈
        closedBall (x₀, ContinuousLinearMap.id ℝ X)
          (H.initialRadius : ℝ) := by
    rw [Metric.mem_closedBall] at hqClosed ⊢
    rw [Prod.dist_eq, dist_self]
    rw [max_eq_left (dist_nonneg : 0 ≤ dist q x₀)]
    exact hqClosed
  have hAugData := H.selector_data
    (q, ContinuousLinearMap.id ℝ X) hqAug
  have hPsiD : ∀ᶠ h in nhds (0 : X),
      Psi h 0 = ContinuousLinearMap.id ℝ X h ∧
        (∀ tau ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Psi h)
            (fderiv ℝ F (B.selector q tau) (Psi h tau))
            (Icc (0 : ℝ) T) tau) ∧
        Psi h t = D h := by
    apply Filter.Eventually.of_forall
    intro h
    refine ⟨?_, ?_, ?_⟩
    · have hinitial := congrArg Prod.snd hAugData.1
      simpa only [Psi, ContinuousLinearMap.id_apply] using
        congrArg (fun A : X →L[ℝ] X ↦ A h) hinitial
    · intro tau htau
      have hstate := (hAugData.2.1 tau (htimeSubset htau)).mono htimeSubset
      have hopen : HasDerivWithinAt
          (fun s : ℝ ↦
            (H.selector (q, ContinuousLinearMap.id ℝ X) s).2)
          ((fderiv ℝ F
              (H.selector (q, ContinuousLinearMap.id ℝ X) tau).1).comp
            (H.selector (q, ContinuousLinearMap.id ℝ X) tau).2)
          (Icc (0 : ℝ) T) tau := by
        have hraw := hstate.hasFDerivWithinAt.snd.hasDerivWithinAt
        convert hraw using 1 <;>
          simp [firstVariationalAugmentedField]
      have hconst : HasDerivWithinAt (fun _ : ℝ ↦ h) 0
          (Icc (0 : ℝ) T) tau :=
        (hasDerivAt_const tau h).hasDerivWithinAt
      have happ := hopen.clm_apply hconst
      simpa only [Psi, B, projectFirstVariational_selector,
        firstVariationalAugmentedField, ContinuousLinearMap.comp_apply,
        map_zero, add_zero] using happ
    · rfl
  have hresult :=
    parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually_nestedBalls
      (F := F) (beta := B.selector) (q := q)
      (J := ContinuousLinearMap.id ℝ X) (Psi := Psi) (D := D)
      (T := T) (inner := B.protectedInnerRadius)
      (outer := (B.tubeRadius : ℝ)) (K := B.lipschitzConstant)
      (p := x₀) (t := t)
      hT B.protectedInnerRadius_lt_tubeRadius B.field_lipschitzOn
      B.uniform_taylor_remainder_on_tube
      hbaseDer hbaseMem hpert hPsiD ht
  simpa only [B, D] using hresult

end LocalRegularControlledContinuousAutonomousSelector

end OneVariationalLevel

end Poincare
