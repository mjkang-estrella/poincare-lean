import Poincare.Global.FinalSelector

/-!
# Scalar norm-system operator bound

This module bounds the time-independent scalar Jacobi norm-system operator used
by the selector stack.  The active speed-generic form is
`(a, b, c) ↦ (2 b, c - speed ^ 2 * a, -2 * speed ^ 2 * b)`, so its operator
norm is controlled by an explicit scalar depending only on `speed ^ 2`.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

namespace Poincare
namespace AopBound

local notation "Triple" => ℝ × ℝ × ℝ

/-- Component bound for the speed-generic scalar norm-system operator. -/
theorem speed_normSystem_opNorm_le_of_speed_sq_le
    {speed S : ℝ} (hS_one : 1 ≤ S) (hspeed_sq : speed ^ 2 ≤ S)
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)) :
    ‖Aop‖ ≤ 4 * S := by
  have hS_nonneg : 0 ≤ S := le_trans zero_le_one hS_one
  have hbound_nonneg : 0 ≤ 4 * S := by nlinarith
  refine ContinuousLinearMap.opNorm_le_bound Aop hbound_nonneg ?_
  intro x
  have hx₁ : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have hx₂ : ‖x.2.1‖ ≤ ‖x‖ :=
    (norm_fst_le x.2).trans (norm_snd_le x)
  have hx₃ : ‖x.2.2‖ ≤ ‖x‖ :=
    (norm_snd_le x.2).trans (norm_snd_le x)
  have hfirst : ‖2 * x.2.1‖ ≤ (4 * S) * ‖x‖ := by
    calc
      ‖2 * x.2.1‖ = 2 * ‖x.2.1‖ := by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left hx₂ (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ (4 * S) * ‖x‖ := by
        have hcoef : 2 ≤ 4 * S := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
  have hspeed_coeff :
      ‖speed ^ 2 * x.1‖ = speed ^ 2 * ‖x.1‖ := by
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg speed)]
  have hspeed_x₁ : speed ^ 2 * ‖x.1‖ ≤ S * ‖x‖ :=
    mul_le_mul hspeed_sq hx₁ (norm_nonneg x.1) hS_nonneg
  have hsecond : ‖x.2.2 - speed ^ 2 * x.1‖ ≤ (4 * S) * ‖x‖ := by
    calc
      ‖x.2.2 - speed ^ 2 * x.1‖ ≤ ‖x.2.2‖ + ‖speed ^ 2 * x.1‖ :=
        norm_sub_le x.2.2 (speed ^ 2 * x.1)
      _ = ‖x.2.2‖ + speed ^ 2 * ‖x.1‖ := by rw [hspeed_coeff]
      _ ≤ ‖x‖ + S * ‖x‖ := add_le_add hx₃ hspeed_x₁
      _ = (1 + S) * ‖x‖ := by ring
      _ ≤ (4 * S) * ‖x‖ := by
        have hcoef : 1 + S ≤ 4 * S := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
  have hthird_coeff :
      ‖(-2 * speed ^ 2 : ℝ)‖ = 2 * speed ^ 2 := by
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg speed)]
    norm_num
  have hthird : ‖-2 * speed ^ 2 * x.2.1‖ ≤ (4 * S) * ‖x‖ := by
    calc
      ‖-2 * speed ^ 2 * x.2.1‖ =
          (2 * speed ^ 2) * ‖x.2.1‖ := by
        rw [norm_mul, hthird_coeff]
      _ ≤ (2 * S) * ‖x‖ := by
        have hcoef : 2 * speed ^ 2 ≤ 2 * S := by nlinarith [sq_nonneg speed]
        exact mul_le_mul hcoef hx₂ (norm_nonneg x.2.1) (by nlinarith [sq_nonneg speed])
      _ ≤ (4 * S) * ‖x‖ := by
        have hcoef : 2 * S ≤ 4 * S := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
  have htail :
      ‖((x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1) : ℝ × ℝ)‖ ≤
        (4 * S) * ‖x‖ := by
    rw [Prod.norm_mk]
    exact max_le hsecond hthird
  have htriple :
      ‖((2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
          -2 * speed ^ 2 * x.2.1) : Triple)‖ ≤ (4 * S) * ‖x‖ := by
    rw [Prod.norm_mk]
    exact max_le hfirst htail
  simpa [hAop x] using htriple

/-- Explicit operator-norm bound in terms of the actual speed. -/
theorem speed_normSystem_opNorm_le
    (speed : ℝ) (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)) :
    ‖Aop‖ ≤ 4 * max (1 : ℝ) (speed ^ 2) :=
  speed_normSystem_opNorm_le_of_speed_sq_le
    (speed := speed) (S := max (1 : ℝ) (speed ^ 2))
    (le_max_left _ _) (le_max_right _ _) Aop hAop

/-- Operator-norm bound from any exported upper bound on `speed ^ 2`. -/
theorem speed_normSystem_opNorm_le_of_speed_sq_bound
    {speed S : ℝ} (hspeed_sq : speed ^ 2 ≤ S)
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)) :
    ‖Aop‖ ≤ 4 * max (1 : ℝ) S :=
  speed_normSystem_opNorm_le_of_speed_sq_le
    (speed := speed) (S := max (1 : ℝ) S)
    (le_max_left _ _) (hspeed_sq.trans (le_max_right _ _)) Aop hAop

/-- The constant-coefficient unit-speed norm system has absolute operator norm at most `4`. -/
theorem unit_normSystem_opNorm_le_four
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1)) :
    ‖Aop‖ ≤ 4 := by
  have hshape : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - (1 : ℝ) ^ 2 * x.1,
        -2 * (1 : ℝ) ^ 2 * x.2.1) := by
    intro x
    simpa using hAop x
  simpa using speed_normSystem_opNorm_le (speed := 1) Aop hshape

/-- A non-vacuous scalar bound package for the speed-generic norm-system operator. -/
theorem exists_speed_normSystem_bound
    (speed : ℝ) (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)) :
    ∃ Cscalar : ℝ, 0 ≤ Cscalar ∧ ‖Aop‖ ≤ Cscalar := by
  refine ⟨4 * max (1 : ℝ) (speed ^ 2), ?_, speed_normSystem_opNorm_le speed Aop hAop⟩
  have hmax_nonneg : 0 ≤ max (1 : ℝ) (speed ^ 2) :=
    le_trans zero_le_one (le_max_left _ _)
  nlinarith

/--
Coefficient-time shrink from the explicit speed-generic operator bound and an
extra common-time floor.
-/
theorem speed_normSystem_mul_time_le_half
    {speed T : ℝ} (hT_nonneg : 0 ≤ T) (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hT :
      T ≤ 1 / (2 * (4 * max (1 : ℝ) (speed ^ 2) + 1))) :
    ‖Aop‖ * T ≤ (1 : ℝ) / 2 := by
  let C : ℝ := 4 * max (1 : ℝ) (speed ^ 2)
  have hC_nonneg : 0 ≤ C := by
    have hmax_nonneg : 0 ≤ max (1 : ℝ) (speed ^ 2) :=
      le_trans zero_le_one (le_max_left _ _)
    dsimp [C]
    nlinarith
  have hAopNorm : ‖Aop‖ ≤ C := by
    simpa [C] using speed_normSystem_opNorm_le speed Aop hAop
  calc
    ‖Aop‖ * T ≤ C * T := mul_le_mul_of_nonneg_right hAopNorm hT_nonneg
    _ ≤ (1 : ℝ) / 2 :=
      FinalSelector.coeff_mul_time_le_half_of_le_inv_two_mul_add_one
        (C := C) (T := T) hC_nonneg (by simpa [C] using hT)

/--
Coefficient-time shrink from an external upper bound on `speed ^ 2`, matching
the hosted speed-bound exports.
-/
theorem speed_normSystem_mul_time_le_half_of_speed_sq_bound
    {speed S T : ℝ} (hspeed_sq : speed ^ 2 ≤ S) (hT_nonneg : 0 ≤ T)
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hT : T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1))) :
    ‖Aop‖ * T ≤ (1 : ℝ) / 2 := by
  let C : ℝ := 4 * max (1 : ℝ) S
  have hC_nonneg : 0 ≤ C := by
    have hmax_nonneg : 0 ≤ max (1 : ℝ) S :=
      le_trans zero_le_one (le_max_left _ _)
    dsimp [C]
    nlinarith
  have hAopNorm : ‖Aop‖ ≤ C := by
    simpa [C] using
      speed_normSystem_opNorm_le_of_speed_sq_bound
        (speed := speed) (S := S) hspeed_sq Aop hAop
  calc
    ‖Aop‖ * T ≤ C * T := mul_le_mul_of_nonneg_right hAopNorm hT_nonneg
    _ ≤ (1 : ℝ) / 2 :=
      FinalSelector.coeff_mul_time_le_half_of_le_inv_two_mul_add_one
        (C := C) (T := T) hC_nonneg (by simpa [C] using hT)

end AopBound
end Poincare
