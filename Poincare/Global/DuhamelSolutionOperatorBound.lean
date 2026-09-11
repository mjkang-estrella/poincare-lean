import Poincare.Global.MovingLimitLeibniz
import Poincare.Global.DuhamelParabolicHolderSeminorm
import Poincare.Global.ParabolicSolutionGraph

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval Laplacian

namespace Poincare.DuhamelSolutionOperatorBound

local notation "E" => Poincare.ClosedSmoothModel 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

open HeatDuhamelHessianDifferentiation HeatDuhamelHeatEquation ParabolicHolder

/-- The three coordinate diagonal evaluations are bounded by three operator norms. -/
theorem abs_trace_le (A : E →L[ℝ] E →L[ℝ] ℝ) :
    |∑ i : Fin 3, A (e i) (e i)| ≤ 3 * ‖A‖ := by
  calc
    |∑ i : Fin 3, A (e i) (e i)| ≤ ∑ i : Fin 3, ‖A (e i) (e i)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i : Fin 3 => A (e i) (e i))
    _ ≤ ∑ _i : Fin 3, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
        ContinuousLinearMap.le_opNorm₂ A (e i) (e i)
    _ = 3 * ‖A‖ := by simp

/-- The within-interval time derivative has the expected sup estimate. -/
theorem duhamel_time_derivative_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    ∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun r => u r x) (f (t,x) + (Δ (u t)) x) (Icc 0 T) t ∧
      |f (t,x) + (Δ (u t)) x| ≤ M + 3 * C * K * t ^ (α / 2) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro t ht x
  have hd := (MovingLimitLeibniz.duhamel_solves_heat_equation
    α hα hα1 T hT hT1 f M K hM hK hf hfM hfK).2 t ht x
  rw [← laplacian_eq_hessian_trace] at hd
  refine ⟨hd, ?_⟩
  have hb := ((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht x).2.2.2
  rw [laplacian_eq_hessian_trace]
  calc
    _ ≤ |f (t,x)| + 3 * ‖fderiv ℝ (fderiv ℝ (fun z : E =>
        ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) z)) x‖ :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_trace_le _))
    _ ≤ M + 3 * (C * K * t ^ (α / 2)) :=
      add_le_add (hfM t ht x) (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = M + 3 * C * K * t ^ (α / 2) := by ring

/-- Tracing the parabolic Hessian increment controls the time derivative increment. -/
theorem duhamel_time_derivative_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    HasHolderBound α (cylinder T) f K →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    HasHolderBound α (cylinder T) (fun p => f p + (Δ (u p.1)) p.2)
      (K + 3 * C * K) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ :=
    DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hb := hCb T hT hT1 f M K hM hK hf hfM hspace p hp q hq
  have htrace : |(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2| ≤
      3 * ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 -
        fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
    simpa only [laplacian_eq_hessian_trace, ContinuousLinearMap.sub_apply,
      Finset.sum_sub_distrib] using abs_trace_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
  change ‖(f p + (Δ (u p.1)) p.2) - (f q + (Δ (u q.1)) q.2)‖ ≤ _
  rw [add_sub_add_comm]
  calc
    _ ≤ ‖f p - f q‖ + ‖(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2‖ := norm_add_le _ _
    _ ≤ K * parabolicDist p q ^ α + 3 * (C * K * parabolicDist p q ^ α) :=
      add_le_add (hfK p hp q hq)
        (htrace.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
    _ = (K + 3 * C * K) * parabolicDist p q ^ α := by ring

/-- Integrating the gradient kernel gives the sharp square-root time factor. -/
theorem duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
    ‖fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t-s) (fun y => f (s,y)) z) x‖ ≤
      2 * M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * Real.sqrt t := by
  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
  let A := M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖)
  have hb : ‖∫ s in (0 : ℝ)..t,
      fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) x‖ ≤
      ∫ s in (0 : ℝ)..t, A * (t-s) ^ (-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
      ← restrict_Ioo_eq_restrict_Ioc]
    apply MeasureTheory.norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
        (intervalIntegrable_gradient_majorant t A))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s,y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) hc.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hM s hsT) x
  have he := HeatDuhamelSpatialHolderHessian.integral_hessian_majorant zero_lt_one t A
  norm_num only [div_one, show (1 : ℝ) / 2 - 1 = -(1/2 : ℝ) by norm_num] at he
  rw [he] at hb
  simpa [A, Real.sqrt_eq_rpow, mul_assoc, mul_left_comm, mul_comm] using hb

/-- A uniform time-derivative bound controls all value increments and the initial trace. -/
theorem duhamel_value_time_estimates :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    (∀ t ∈ Icc 0 T, ∀ x : E, |u t x| ≤ t * (M + 3 * C * K * T ^ (α/2))) ∧
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x : E,
      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s|) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hd := hCb T hT hT1 f M K hM hK hf hfM hfK
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) (x : E) :
      ‖f (r,x) + (Δ (u r)) x‖ ≤ M + 3 * C * K * T ^ (α/2) := by
    apply (hd r hr x).2.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.1 hr.2 (by linarith)) (by positivity))
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr => (hd r hr x).1) (fun r hr => hb r hr x) (convex_Icc (0 : ℝ) T) hs ht
  refine ⟨?_, hi⟩
  intro t ht x
  simpa [u, abs_of_nonneg ht.1, mul_comm] using hi t ht 0 ⟨le_rfl, hT.le⟩ x

end Poincare.DuhamelSolutionOperatorBound
