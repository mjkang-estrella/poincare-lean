import Poincare.Global.SmoothInitialMetricDefinitions
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Bornology
set_option autoImplicit false
universe v

namespace Poincare.SmoothInitialMetricPositiveCone

/-- Positive symmetric continuous bilinear forms are preserved by convex combinations. -/
theorem convex_positiveSymmetricBilinearForms
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Convex ℝ (SmoothInitialMetricDefinitions.positiveSymmetricBilinearForms V) := by
  rw [convex_iff_forall_pos]
  rintro q ⟨hq_symm, hq_pos⟩ r ⟨hr_symm, hr_pos⟩ a b ha hb _
  constructor
  · intro x y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hq_symm x y, hr_symm x y]
  · intro x hx
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] using add_pos (mul_pos ha (hq_pos x hx)) (mul_pos hb (hr_pos x hx))

/-- Strict diagonal positivity is uniformly coercive on a finite-dimensional real space. -/
theorem exists_pos_mul_norm_sq_le
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (q : V →L[ℝ] V →L[ℝ] ℝ) (hq : ∀ x, x ≠ 0 → 0 < q x x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ q x x := by
  have hcont : Continuous (fun x : V => q x x) :=
    q.continuous.clm_apply continuous_id
  obtain ⟨c, hc, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le'
    hcont.continuousOn (fun x hx => hq x (by
      have : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
      intro hx0
      simp [hx0] at this))
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : V := ‖x‖⁻¹ • x
  have hy : y ∈ Metric.sphere (0 : V) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, y, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]
  have hxy : ‖x‖ • y = x := by simp [y, smul_smul, hn]
  have hscale : q x x = ‖x‖ ^ 2 * q y y := by
    calc
      q x x = q (‖x‖ • y) (‖x‖ • y) := by rw [hxy]
      _ = ‖x‖ ^ 2 * q y y := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
  rw [hscale, mul_comm c]
  exact mul_le_mul_of_nonneg_left (hmin y hy) (sq_nonneg ‖x‖)

/-- The diagonal unit ball of a positive form is bounded; symmetry is not required. -/
theorem isVonNBounded_bilinear_unitBall
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (q : V →L[ℝ] V →L[ℝ] ℝ) (hq : ∀ x, x ≠ 0 → 0 < q x x) :
    Bornology.IsVonNBounded ℝ {x : V | q x x < 1} := by
  obtain ⟨c, hc, hcoercive⟩ := exists_pos_mul_norm_sq_le q hq
  apply NormedSpace.isVonNBounded_of_isBounded ℝ
  refine isBounded_iff_forall_norm_le.mpr ⟨1 + c⁻¹, fun x hx => ?_⟩
  have hinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  by_contra hbound
  have hlarge : 1 + c⁻¹ < ‖x‖ := lt_of_not_ge hbound
  have hnorm : 1 ≤ ‖x‖ := by linarith
  have hsq : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
  have hlinear : c * ‖x‖ < 1 :=
    lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hsq hc.le).trans (hcoercive x)) hx
  have hlarge_mul := mul_lt_mul_of_pos_left hlarge hc
  nlinarith

end Poincare.SmoothInitialMetricPositiveCone
