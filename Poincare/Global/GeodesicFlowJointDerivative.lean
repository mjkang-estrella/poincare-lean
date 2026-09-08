import Poincare.Global.ParameterizedFlowDerivative
import Poincare.Global.LinearEndpointGronwall

/-!
# Joint initial-state variations of a fixed-chart geodesic flow

The variational unknown is a continuous linear endomorphism of the entire
position-velocity state space. Its initial value is the identity.
-/

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Asymptotics Filter Function Metric Set
open scoped Topology NNReal ContDiff Manifold

namespace Poincare
namespace GeodesicFlowJointDerivative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bounded continuous coefficient admits an operator-valued fundamental
solution on a prescribed short interval. Every initial direction, including
both position and velocity, is evaluated from the same operator solution. -/
theorem exists_fundamentalSolution_on_prescribed_Icc [CompleteSpace X]
    {A : ℝ → X →L[ℝ] X} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc (-T) T)) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ (K : ℝ))
    (hKT : (K : ℝ) * T ≤ 1 / 4) :
    ∃ Φ : ℝ → X →L[ℝ] X,
      Φ 0 = ContinuousLinearMap.id ℝ X ∧
      (∀ t ∈ Icc (-T) T, HasDerivWithinAt Φ ((A t).comp (Φ t))
        (Icc (-T) T) t) ∧
      ∀ h : X, ∀ t ∈ Icc (-T) T,
        HasDerivWithinAt (fun s => Φ s h) (A t (Φ t h)) (Icc (-T) T) t := by
  let B : ℝ → (X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
    fun t => ContinuousLinearMap.compL ℝ X X X (A t)
  have hB : ∀ t ∈ Icc (-T) T, ‖B t‖ ≤ (K : ℝ) := by
    intro t ht
    calc
      ‖B t‖ ≤ (1 : ℝ) * ‖A t‖ :=
        by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ X X X)
              (norm_nonneg _))
      _ ≤ 1 * (K : ℝ) := mul_le_mul_of_nonneg_left (hK t ht) zero_le_one
      _ = (K : ℝ) := one_mul _
  have hpl : IsPicardLindelof (fun t Y => B t Y)
      (tmin := -T) (tmax := T) ⟨0, by constructor <;> linarith⟩
      (ContinuousLinearMap.id ℝ X) 1 (1 / 2) (2 * K) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hB t ht)).lipschitzOnWith
    · intro Y _
      exact ((ContinuousLinearMap.compL ℝ X X X).continuous.comp_continuousOn hA).clm_apply
        continuousOn_const
    · intro t ht Y hY
      have hYnorm : ‖Y‖ ≤ 2 := by
        have hd : ‖Y - ContinuousLinearMap.id ℝ X‖ ≤ 1 := by
          simpa [mem_closedBall, dist_eq_norm] using hY
        exact (norm_le_norm_sub_add Y (ContinuousLinearMap.id ℝ X)).trans
          (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := X)])
      calc
        ‖B t Y‖ ≤ ‖B t‖ * ‖Y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K : ℝ) * 2 := mul_le_mul (hB t ht) hYnorm (norm_nonneg _) K.2
        _ = ((2 * K : ℝ≥0) : ℝ) := by simp; ring
    · simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_mul,
        NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_div]
      nlinarith
  obtain ⟨Φ, hΦ0, hΦ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (mem_closedBall_self (by positivity))
  refine ⟨Φ, hΦ0, hΦ, ?_⟩
  intro h t ht
  simpa [B] using (hΦ t ht).clm_apply (hasDerivWithinAt_const t (Icc (-T) T) h)

/-- The Gronwall residual theorem with the identity initial-state injection.
The perturbation ranges over the whole state space. -/
theorem initialState_residual_isLittleO [ProperSpace X]
    {F : X → X} (hF : ContDiff ℝ 1 F)
    {α : X → ℝ → X} {Φ : ℝ → X →L[ℝ] X}
    {p q : X} {r a T t : ℝ} (hT : 0 < T) (hq : q ∈ ball p r)
    (hα : ∀ y ∈ ball p r, α y 0 = y ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (α y) (F (α y s)) (Icc 0 T) s) ∧
      ∀ s ∈ Icc 0 T, α y s ∈ closedBall p a)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ X)
    (hΦ : ∀ s ∈ Icc 0 T, HasDerivWithinAt Φ
      ((fderiv ℝ F (α q s)).comp (Φ s)) (Icc 0 T) s)
    (ht : t ∈ Icc 0 T) :
    (fun h : X => α (q + h) t - α q t - Φ t h) =o[𝓝 (0 : X)] (fun h => h) := by
  obtain ⟨K, hLip⟩ := hF.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall p (a + 1)) (isCompact_closedBall p (a + 1))
  have hpert : ∀ᶠ h in 𝓝 (0 : X),
      α (q + h) 0 = α q 0 + (ContinuousLinearMap.id ℝ X) h ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (α (q + h)) (F (α (q + h) s))
        (Icc 0 T) s) ∧ ∀ s ∈ Icc 0 T, α (q + h) s ∈ closedBall p a := by
    have hnear : ∀ᶠ h in 𝓝 (0 : X), q + h ∈ ball p r :=
      (continuousAt_const.add continuousAt_id).preimage_mem_nhds
        (by simpa using isOpen_ball.mem_nhds hq)
    filter_upwards [hnear] with h hh
    exact ⟨by simp [(hα (q + h) hh).1, (hα q hq).1], (hα (q + h) hh).2⟩
  have hlin : ∀ᶠ h in 𝓝 (0 : X),
      Φ 0 h = (ContinuousLinearMap.id ℝ X) h ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => Φ s h)
        (fderiv ℝ F (α q s) (Φ s h)) (Icc 0 T) s) ∧ Φ t h = Φ t h := by
    apply Filter.Eventually.of_forall
    intro h
    refine ⟨by rw [hΦ0], ?_, rfl⟩
    intro s hs
    simpa using (hΦ s hs).clm_apply (hasDerivWithinAt_const s (Icc 0 T) h)
  have hd := parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
    (J := ContinuousLinearMap.id ℝ X) (Ψ := fun h s => Φ s h)
    hT hLip
    (uniform_taylor_remainder_norm_le_on_compact_convex hF
      (isCompact_closedBall p (a + 1)) (convex_closedBall p (a + 1)))
    (hα q hq).2.1 (hα q hq).2.2 hpert hlin ht
  exact hasFDerivAt_iff_isLittleO_nhds_zero.mp hd

end GeodesicFlowJointDerivative
end Poincare
