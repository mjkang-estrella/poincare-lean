import Poincare.Global.GeodesicLinearized

/-!
# Prescribed-interval linear ODE package

The generic local Picard--Lindelof constructor chooses its own time interval.
For uniform flow towers it is more useful to prescribe a sufficiently short
interval after a coefficient bound has been chosen.  The zero-centered linear
case admits a direct package with the single smallness condition `K*T ≤ 1/2`.
-/

noncomputable section

open Metric Set
open scoped NNReal Topology

namespace Poincare

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
A continuous linear ODE with coefficient norm at most `K` has a
zero-centered Picard--Lindelof package on the prescribed symmetric interval
`[-T,T]` whenever `K*T ≤ 1/2`.
-/
theorem isPicardLindelof_continuous_linearODE_zero_on_prescribed_Icc
    (A : ℝ → X →L[ℝ] X) (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) (K : ℝ≥0)
    (hAop : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ (K : ℝ))
    (hKT : (K : ℝ) * T ≤ (1 : ℝ) / 2) :
    IsPicardLindelof (fun t x => A t x)
      (tmin := -T) (tmax := T)
      ⟨(0 : ℝ), by constructor <;> linarith⟩ (0 : X)
      (1 : ℝ≥0) (1 / 2 : ℝ≥0) K K := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t ht
    exact
      (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAop t ht)).lipschitzOnWith
  · intro x _hx
    exact (hA.clm_apply continuous_const).continuousOn
  · intro t ht x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    calc
      ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A t) x
      _ ≤ (K : ℝ) * 1 := mul_le_mul (hAop t ht) hxnorm
        (norm_nonneg x) K.2
      _ = (K : ℝ) := by ring
  · simp only [NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_one, sub_zero, zero_sub, neg_neg]
    rw [max_eq_left (le_rfl : T ≤ T)]
    norm_num
    exact hKT

end Poincare
