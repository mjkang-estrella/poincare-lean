import Poincare.Global.SpeedGeneric

/-!
# Closed-ball bounds for pinned Jacobi norm trajectories

This module records the explicit boundedness of the speed-pinned scalar
trajectory used by the norm-system Picard-Lindelöf packages.  It is deliberately
only about the pinned trajectory: the current `actual_jacobi_norms_eq_*`
theorems consume actual closed-ball membership as an input, so using those
theorems to prove the actual membership would be circular.
-/

noncomputable section

open Metric Set
open scoped NNReal

namespace Poincare
namespace MembershipBound

local notation "Triple" => ℝ × ℝ × ℝ

/--
A uniform-in-time radius for the speed-pinned norm-system trajectory centered
at `(0, 0, q)`.

The three terms separately bound `|a|`, `|b|`, and `|c - q|` for
`a = sin(speed * t)^2 / speed^2 * q`,
`b = sin(speed * t) cos(speed * t) / speed * q`, and
`c = cos(speed * t)^2 * q`.
-/
def speedPinnedMembershipRadius (speed q : ℝ) : ℝ≥0 :=
  ⟨max (max (|(speed ^ 2)⁻¹| * |q|) (|speed⁻¹| * |q|)) (2 * |q|), by positivity⟩

private theorem abs_speedPinnedA_le_radius (speed q t : ℝ) :
    |JacobiNormSystem.speedPinnedA speed q t| ≤
      (speedPinnedMembershipRadius speed q : ℝ) := by
  have hsin_sq_le : |Real.sin (speed * t)| ^ 2 ≤ 1 := by
    have hsin := Real.abs_sin_le_one (speed * t)
    have hsin_nonneg : 0 ≤ |Real.sin (speed * t)| := abs_nonneg _
    nlinarith
  have hA :
      |JacobiNormSystem.speedPinnedA speed q t| ≤ |(speed ^ 2)⁻¹| * |q| := by
    rw [JacobiNormSystem.speedPinnedA, JacobiNormSystem.speedPinnedScale]
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |Real.sin (speed * t)| ^ 2 * |(speed ^ 2)⁻¹| * |q| ≤
          1 * |(speed ^ 2)⁻¹| * |q| := by
            gcongr
      _ = |(speed ^ 2)⁻¹| * |q| := by ring
  exact hA.trans (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem abs_speedPinnedB_le_radius (speed q t : ℝ) :
    |JacobiNormSystem.speedPinnedB speed q t| ≤
      (speedPinnedMembershipRadius speed q : ℝ) := by
  have hsin := Real.abs_sin_le_one (speed * t)
  have hcos := Real.abs_cos_le_one (speed * t)
  have hsin_cos_le : |Real.sin (speed * t) * Real.cos (speed * t)| ≤ 1 := by
    rw [abs_mul]
    have hsin_nonneg : 0 ≤ |Real.sin (speed * t)| := abs_nonneg _
    have hcos_nonneg : 0 ≤ |Real.cos (speed * t)| := abs_nonneg _
    nlinarith [mul_le_mul hsin hcos hcos_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  have hB :
      |JacobiNormSystem.speedPinnedB speed q t| ≤ |speed⁻¹| * |q| := by
    rw [JacobiNormSystem.speedPinnedB, abs_mul]
    calc
      |Real.sin (speed * t) * Real.cos (speed * t)| * |speed⁻¹ * q| ≤
          1 * |speed⁻¹ * q| := by
            gcongr
      _ = |speed⁻¹| * |q| := by rw [abs_mul, one_mul]
  exact hB.trans (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem abs_speedPinnedC_sub_q_le_radius (speed q t : ℝ) :
    |JacobiNormSystem.speedPinnedC speed q t - q| ≤
      (speedPinnedMembershipRadius speed q : ℝ) := by
  have hcos_sq_le : |Real.cos (speed * t)| ^ 2 ≤ 1 := by
    have hcos := Real.abs_cos_le_one (speed * t)
    have hcos_nonneg : 0 ≤ |Real.cos (speed * t)| := abs_nonneg _
    nlinarith
  have hC : |JacobiNormSystem.speedPinnedC speed q t| ≤ |q| := by
    rw [JacobiNormSystem.speedPinnedC, abs_mul, abs_pow]
    calc
      |Real.cos (speed * t)| ^ 2 * |q| ≤ 1 * |q| := by
        gcongr
      _ = |q| := by ring
  have hsub : |JacobiNormSystem.speedPinnedC speed q t - q| ≤ 2 * |q| := by
    calc
      |JacobiNormSystem.speedPinnedC speed q t - q| ≤
          |JacobiNormSystem.speedPinnedC speed q t| + |q| := by
            simpa using
              (abs_sub_le (JacobiNormSystem.speedPinnedC speed q t) (0 : ℝ) q)
      _ ≤ |q| + |q| := by gcongr
      _ = 2 * |q| := by ring
  exact hsub.trans (le_max_right _ _)

/--
The speed-pinned norm-system state lies in the closed ball of the explicit
radius `speedPinnedMembershipRadius speed q` around `(0, 0, q)`, uniformly in
time.
-/
theorem speedPinned_mem_closedBall (speed q t : ℝ) :
    ((JacobiNormSystem.speedPinnedA speed q t,
        JacobiNormSystem.speedPinnedB speed q t,
        JacobiNormSystem.speedPinnedC speed q t) : Triple) ∈
      closedBall (((0 : ℝ), (0 : ℝ), q) : Triple)
        (speedPinnedMembershipRadius speed q : ℝ) := by
  rw [mem_closedBall, dist_eq_norm]
  simp [Prod.norm_mk, Real.norm_eq_abs,
    abs_speedPinnedA_le_radius, abs_speedPinnedB_le_radius,
    abs_speedPinnedC_sub_q_le_radius]

/--
The pinned trajectory remains in any larger fixed closed-ball radius.  This is
the form to use when a surrounding Picard-Lindelöf package has already chosen
its radius.
-/
theorem speedPinned_mem_closedBall_of_radius_ge
    {speed q t : ℝ} {radius : ℝ≥0}
    (hradius : (speedPinnedMembershipRadius speed q : ℝ) ≤ (radius : ℝ)) :
    ((JacobiNormSystem.speedPinnedA speed q t,
        JacobiNormSystem.speedPinnedB speed q t,
        JacobiNormSystem.speedPinnedC speed q t) : Triple) ∈
      closedBall (((0 : ℝ), (0 : ℝ), q) : Triple) (radius : ℝ) := by
  have hmem := speedPinned_mem_closedBall speed q t
  rw [mem_closedBall] at hmem ⊢
  exact hmem.trans hradius

/--
Interval form of `speedPinned_mem_closedBall`, matching the membership shape
expected by the speed-generic norm-system consumers.
-/
theorem speedPinned_mem_closedBall_on_Icc
    {tmin tmax speed q : ℝ} :
    ∀ t ∈ Icc tmin tmax,
      ((JacobiNormSystem.speedPinnedA speed q t,
          JacobiNormSystem.speedPinnedB speed q t,
          JacobiNormSystem.speedPinnedC speed q t) : Triple) ∈
        closedBall (((0 : ℝ), (0 : ℝ), q) : Triple)
          (speedPinnedMembershipRadius speed q : ℝ) := by
  intro t _ht
  exact speedPinned_mem_closedBall speed q t

/--
Interval form with a larger fixed radius side condition.
-/
theorem speedPinned_mem_closedBall_on_Icc_of_radius_ge
    {tmin tmax speed q : ℝ} {radius : ℝ≥0}
    (hradius : (speedPinnedMembershipRadius speed q : ℝ) ≤ (radius : ℝ)) :
    ∀ t ∈ Icc tmin tmax,
      ((JacobiNormSystem.speedPinnedA speed q t,
          JacobiNormSystem.speedPinnedB speed q t,
          JacobiNormSystem.speedPinnedC speed q t) : Triple) ∈
        closedBall (((0 : ℝ), (0 : ℝ), q) : Triple) (radius : ℝ) := by
  intro t _ht
  exact speedPinned_mem_closedBall_of_radius_ge (speed := speed) (q := q)
    (t := t) (radius := radius) hradius

/--
If an actual norm-system state is already identified with the speed-pinned
state, then it inherits the explicit closed-ball membership.
-/
theorem actual_state_mem_closedBall_of_eq_speedPinned
    {speed q t a b c : ℝ}
    (ha : a = JacobiNormSystem.speedPinnedA speed q t)
    (hb : b = JacobiNormSystem.speedPinnedB speed q t)
    (hc : c = JacobiNormSystem.speedPinnedC speed q t) :
    ((a, b, c) : Triple) ∈
      closedBall (((0 : ℝ), (0 : ℝ), q) : Triple)
        (speedPinnedMembershipRadius speed q : ℝ) := by
  simpa [ha, hb, hc] using speedPinned_mem_closedBall speed q t

/--
Fixed-radius version of `actual_state_mem_closedBall_of_eq_speedPinned`.
-/
theorem actual_state_mem_closedBall_of_eq_speedPinned_of_radius_ge
    {speed q t a b c : ℝ} {radius : ℝ≥0}
    (hradius : (speedPinnedMembershipRadius speed q : ℝ) ≤ (radius : ℝ))
    (ha : a = JacobiNormSystem.speedPinnedA speed q t)
    (hb : b = JacobiNormSystem.speedPinnedB speed q t)
    (hc : c = JacobiNormSystem.speedPinnedC speed q t) :
    ((a, b, c) : Triple) ∈
      closedBall (((0 : ℝ), (0 : ℝ), q) : Triple) (radius : ℝ) := by
  have hmem := actual_state_mem_closedBall_of_eq_speedPinned
    (speed := speed) (q := q) (t := t) (a := a) (b := b) (c := c) ha hb hc
  rw [mem_closedBall] at hmem ⊢
  exact hmem.trans hradius

end MembershipBound
end Poincare
