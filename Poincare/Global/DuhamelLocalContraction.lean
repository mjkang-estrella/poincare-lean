import Poincare.Global.DuhamelContraction

/-!
# Local Duhamel contraction on invariant state balls

Quasilinear and quadratic parabolic nonlinearities are not globally
Lipschitz.  This module localizes the `T A L` estimate: if two paths stay in a
uniform ball around a constant state and the nonlinearity is Lipschitz on that
state ball, the same Duhamel contraction estimate holds.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal

namespace Poincare

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Constant path in an arbitrary topological vector space. -/
def constantDuhamelPathGeneric (T : ℝ≥0) (x₀ : X) : DuhamelPath T X :=
  ContinuousMap.const _ x₀

@[simp]
theorem constantDuhamelPathGeneric_apply
    (T : ℝ≥0) (x₀ : X) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    constantDuhamelPathGeneric T x₀ t = x₀ :=
  rfl

/-- Membership in a uniform path ball implies membership of each evaluation
in the corresponding state-space ball. -/
theorem eval_mem_closedBall_of_path_mem_closedBall
    (T : ℝ≥0) (x₀ : X) {R : ℝ}
    {u : DuhamelPath T X}
    (hu : u ∈ Metric.closedBall (constantDuhamelPathGeneric T x₀) R)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    u t ∈ Metric.closedBall x₀ R := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hu ⊢
  calc
    ‖u t - x₀‖ = ‖(u - constantDuhamelPathGeneric T x₀) t‖ := rfl
    _ ≤ ‖u - constantDuhamelPathGeneric T x₀‖ :=
      ContinuousMap.norm_coe_le_norm _ t
    _ ≤ R := hu

/-- Local version of the `T A L` projected Duhamel estimate. -/
theorem norm_projectedDuhamelDifference_le_of_lipschitzOn_closedBall
    (T A L : ℝ≥0) (S : ℝ → X →L[ℝ] X) (N : X → X)
    (x₀ : X) {R : ℝ}
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ‖S r‖ ≤ (A : ℝ))
    (hN : LipschitzOnWith L N (Metric.closedBall x₀ R))
    (u v : DuhamelPath T X)
    (hu : u ∈ Metric.closedBall (constantDuhamelPathGeneric T x₀) R)
    (hv : v ∈ Metric.closedBall (constantDuhamelPathGeneric T x₀) R)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ‖projectedDuhamelDifference T S N u v t‖ ≤
      ((T * A * L : ℝ≥0) : ℝ) * ‖u - v‖ := by
  let C : ℝ := (A : ℝ) * (L : ℝ) * ‖u - v‖
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖S ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)) -
          N (v (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤ C := by
    intro s hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) (t : ℝ) := by
      simpa [Set.uIoc_of_le t.property.1] using hs
    have hr : (t : ℝ) - s ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
      constructor
      · exact sub_nonneg.mpr hsIoc.2
      · exact (sub_le_self _ hsIoc.1.le).trans t.property.2
    let p : Set.Icc (0 : ℝ) (T : ℝ) :=
      Set.projIcc 0 (T : ℝ) T.property s
    have hup : u p ∈ Metric.closedBall x₀ R :=
      eval_mem_closedBall_of_path_mem_closedBall T x₀ hu p
    have hvp : v p ∈ Metric.closedBall x₀ R :=
      eval_mem_closedBall_of_path_mem_closedBall T x₀ hv p
    have hpath : ‖u p - v p‖ ≤ ‖u - v‖ := by
      simpa using ContinuousMap.norm_coe_le_norm (u - v) p
    have hnonlin : ‖N (u p) - N (v p)‖ ≤ (L : ℝ) * ‖u p - v p‖ := by
      simpa [dist_eq_norm] using hN.dist_le_mul (u p) hup (v p) hvp
    calc
      ‖S ((t : ℝ) - s) (N (u p) - N (v p))‖
          ≤ ‖S ((t : ℝ) - s)‖ * ‖N (u p) - N (v p)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (A : ℝ) * ((L : ℝ) * ‖u p - v p‖) := by
        exact mul_le_mul (hS _ hr) hnonlin (norm_nonneg _) A.property
      _ ≤ (A : ℝ) * ((L : ℝ) * ‖u - v‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpath L.property) A.property
      _ = C := by simp [C, mul_assoc]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [projectedDuhamelDifference]
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        S ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)) -
            N (v (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ C * |(t : ℝ) - 0| := hint
    _ = ((t : ℝ) * (A : ℝ) * (L : ℝ)) * ‖u - v‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      simp [C]
      ring
    _ ≤ ((T : ℝ) * (A : ℝ) * (L : ℝ)) * ‖u - v‖ := by
      gcongr
      exact t.property.2
    _ = ((T * A * L : ℝ≥0) : ℝ) * ‖u - v‖ := by norm_num

end Poincare
