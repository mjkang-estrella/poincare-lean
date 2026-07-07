import Poincare.Global.PLNormFeed

/-!
# Uniform PL data for linear ODEs

The downstream transverse package asks for one Picard-Lindelöf parameter tuple
that works for a family of linear ODE centers.  Coefficient uniformity gives the
Lipschitz constant, but the `IsPicardLindelof.norm_le` field still needs a
uniform bound on the centers themselves.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace Poincare
namespace UniformPL

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
A time-independent linear ODE has a uniform Picard-Lindelöf package for a
family of centers once those centers are uniformly bounded.

This is the non-vacuous piece supplied by linearity: the Lipschitz constant
comes from the single operator norm of `A`, while the vector-field norm bound
uses the separate uniform center bound `hcenter`.
-/
theorem isPicardLindelof_const_linear_uniform_of_center_norm_bound
    (A : X →L[ℝ] X) {ι : Type v} (center : ι → X)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {a r L K B : ℝ≥0}
    (hA : ‖A‖ ≤ (K : ℝ))
    (hcenter : ∀ i, ‖center i‖ + (a : ℝ) ≤ (B : ℝ))
    (hbound : ‖A‖ * (B : ℝ) ≤ (L : ℝ))
    (hmul :
      (L : ℝ) * max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) ≤
        (a : ℝ) - (r : ℝ)) :
    ∀ i : ι,
      IsPicardLindelof
        (fun _ : ℝ => fun x : X => A x)
        (tmin := tmin) (tmax := tmax) t₀ (center i) a r L K := by
  intro i
  refine IsPicardLindelof.of_time_independent (f := fun x : X => A x) ?_ ?_ hmul
  · intro x hx
    have hdist : ‖x - center i‖ ≤ (a : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hxnorm : ‖x‖ ≤ (B : ℝ) := by
      calc
        ‖x‖ ≤ ‖x - center i‖ + ‖center i‖ := norm_le_norm_sub_add x (center i)
        _ ≤ (a : ℝ) + ‖center i‖ := by gcongr
        _ = ‖center i‖ + (a : ℝ) := by ring
        _ ≤ (B : ℝ) := hcenter i
    calc
      ‖A x‖ ≤ ‖A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm A x
      _ ≤ ‖A‖ * (B : ℝ) := by
        gcongr
      _ ≤ (L : ℝ) := hbound
  · exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le hA).lipschitzOnWith

local notation "Triple" => ℝ × ℝ × ℝ

private theorem middle_norm_le_triple_norm (c : ℝ) :
    ‖c‖ ≤ ‖(((0 : ℝ), c, 0) : Triple)‖ :=
  (norm_fst_le ((c, 0) : ℝ × ℝ)).trans
    (norm_snd_le (((0 : ℝ), (c, 0)) : Triple))

/--
The literal oscillator package cannot be uniform over all scalar third
coordinates.  The obstruction is the `norm_le` field of
`IsPicardLindelof`: at the center `(0,0,c)`, the oscillator vector field has
middle component `c`, so no finite `LNorm` can bound all centers.
-/
theorem not_forall_isPicardLindelof_oscillator_scalar_centers
    (speed : ℝ) (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {radius rNorm LNorm KNorm : ℝ≥0} :
    ¬ ∀ c : ℝ,
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ), c) radius rNorm LNorm KNorm := by
  intro hpl
  let c : ℝ := (LNorm : ℝ) + 1
  have hmem :
      ((0 : ℝ), (0 : ℝ), c) ∈
        closedBall (((0 : ℝ), (0 : ℝ), c) : Triple) (radius : ℝ) :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg radius)
  have hle :
      ‖Aop (((0 : ℝ), (0 : ℝ), c) : Triple)‖ ≤ (LNorm : ℝ) :=
    (hpl c).norm_le (0 : ℝ) hzero (((0 : ℝ), (0 : ℝ), c) : Triple) hmem
  have hop :
      Aop (((0 : ℝ), (0 : ℝ), c) : Triple) =
        (((0 : ℝ), c, 0) : Triple) := by
    simpa using hAop (((0 : ℝ), (0 : ℝ), c) : Triple)
  have hmiddle :
      ‖c‖ ≤ ‖Aop (((0 : ℝ), (0 : ℝ), c) : Triple)‖ := by
    rw [hop]
    exact middle_norm_le_triple_norm c
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_le : c ≤ (LNorm : ℝ) := by
    calc
      c = ‖c‖ := (Real.norm_of_nonneg hc_nonneg).symm
      _ ≤ ‖Aop (((0 : ℝ), (0 : ℝ), c) : Triple)‖ := hmiddle
      _ ≤ (LNorm : ℝ) := hle
  dsimp [c] at hc_le
  linarith

end UniformPL
end Poincare
