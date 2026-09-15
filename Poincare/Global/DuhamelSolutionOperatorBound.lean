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

/-- Bounded Lipschitz increments give every intermediate Hölder exponent. -/
theorem holder_of_bounded_lipschitz {F : Type*} [NormedAddCommGroup F]
    {α A B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {g : E → F} (hg : ∀ x, ‖g x‖ ≤ A)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ B * ‖x-y‖) (x y : E) :
    ‖g x - g y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
  by_cases hr : ‖x-y‖ ≤ 1
  · have hp : ‖x-y‖ ≤ ‖x-y‖ ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hr hα hα1
    exact (hlip x y).trans ((mul_le_mul_of_nonneg_left hp hB).trans
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2*A+B)
        (Real.rpow_nonneg (norm_nonneg _) _)))
  · have hp : 1 ≤ ‖x-y‖ ^ α := Real.one_le_rpow (le_of_not_ge hr) hα
    calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2*A := by linarith [hg x, hg y]
      _ ≤ (2*A+B) * ‖x-y‖ ^ α := by
        calc
          2*A ≤ 2*A+B := by linarith
          _ ≤ (2*A+B) * ‖x-y‖ ^ α := le_mul_of_one_le_right (by positivity) hp

/-- The gradient is spatially Hölder with a constant uniform on short time intervals. -/
theorem duhamel_gradient_spatial_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    let u : ℝ → E → ℝ := fun t x =>
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
    ∀ t ∈ Icc 0 T, ∀ x y : E,
      ‖fderiv ℝ (u t) x - fderiv ℝ (u t) y‖ ≤ C * (M+K) * ‖x-y‖ ^ α := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨4*J+C, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro t ht x y
  let u : E → ℝ := fun z => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun w => f (s,w)) z
  have hg (z : E) : ‖fderiv ℝ u z‖ ≤ 2*M*J :=
    (duhamel_gradient_bound ht hf hfM z).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
  have hh (z : E) : ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ C*K :=
    (((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht z).2.2.2).trans
      (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)))
  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
    ((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
      (m := 1) (by norm_num)).differentiable_one
  have hlip (a b : E) : ‖fderiv ℝ u a - fderiv ℝ u b‖ ≤ C*K*‖a-b‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => hh z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ b) (mem_univ a)
  have hb := holder_of_bounded_lipschitz hα.le hα1.le
    (by positivity : 0 ≤ 2*M*J) (by positivity : 0 ≤ C*K) hg hlip x y
  exact hb.trans (mul_le_mul_of_nonneg_right
    (by nlinarith [mul_nonneg hJ hK, mul_nonneg hC.le hM] :
      2*(2*M*J)+C*K ≤ (4*J+C)*(M+K)) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Value increments obey a parabolic Hölder bound uniform for times at most one. -/
theorem duhamel_value_parabolic_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
    HasHolderBound α (cylinder T)
      (fun p : ℝ × E => ∫ s in (0 : ℝ)..p.1,
        heatSolution (p.1-s) (fun y => f (s,y)) p.2) (C * (M+K)) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_value_time_estimates α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨3+9*C+2*J, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  let D := M+3*C*K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd : M+3*C*K*T^(α/2) ≤ D := by
    exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one hT.le hT1 (by linarith)))
  have hv := hCb T hT hT1 f M K hM hK hf hfM hfK
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖u t x‖ ≤ D := by
    exact (hv.1 t ht x).trans ((mul_le_mul_of_nonneg_left hd ht.1).trans
      (mul_le_of_le_one_left hD (ht.2.trans hT1)))
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖fderiv ℝ (u t) x‖ ≤ 2*M*J :=
    (duhamel_gradient_bound ht hf hfM x).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
  intro p hp q hq
  have hs : ‖u p.1 p.2 - u p.1 q.2‖ ≤ (2*D+2*M*J)*‖p.2-q.2‖^α := by
    apply holder_of_bounded_lipschitz hα.le hα1.le hD (by positivity) (hu p.1 hp.1)
    intro a b
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hasFDerivAt_duhamel hp.1 hf hfM z).differentiableAt)
      (fun z _ => hg p.1 hp.1 z) (convex_univ : Convex ℝ (univ : Set E))
      (mem_univ b) (mem_univ a)
  have hab : |p.1-q.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2],
    by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]⟩
  have htp : |p.1-q.1| ≤ parabolicDist p q ^ α := by
    calc
      |p.1-q.1| ≤ |p.1-q.1|^(α/2) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
          (abs_nonneg (p.1-q.1)) hab (by linarith : 0 ≤ α/2) (by linarith : α/2 ≤ 1)
      _ = (Real.sqrt |p.1-q.1|)^α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have ht : ‖u p.1 q.2 - u q.1 q.2‖ ≤ D * parabolicDist p q ^ α :=
    (hv.2 p.1 hp.1 q.1 hq.1 q.2).trans
      ((mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left htp hD))
  calc
    ‖u p.1 p.2 - u q.1 q.2‖ ≤ ‖u p.1 p.2 - u p.1 q.2‖ + ‖u p.1 q.2 - u q.1 q.2‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (2*D+2*M*J)*parabolicDist p q ^ α + D*parabolicDist p q ^ α :=
      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity))) ht
    _ ≤ (3+9*C+2*J)*(M+K)*parabolicDist p q ^ α := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (parabolicDist_nonneg _ _) _)
      dsimp [D]
      nlinarith [mul_nonneg hC.le hM, mul_nonneg hJ hK]

/-- A difference of bounded data has the same gradient kernel estimate. -/
theorem gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
    {f g : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hfM : ∀ y, ‖f y‖ ≤ M)
    (hgN : ∀ y, ‖g y‖ ≤ N) (hL : ∀ y, ‖f y - g y‖ ≤ L) (x : E) :
    ‖fderiv ℝ (heatSolution t f) x - fderiv ℝ (heatSolution t g) x‖ ≤
      L * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1/2 : ℝ)) := by
  have hi := integrable_smul_fderiv_heatKernel_sub ht hf hfM x
  have hj := integrable_smul_fderiv_heatKernel_sub ht hg hgN x
  rw [(heatSolution_hasFDerivAt ht hf hfM x).fderiv,
    (heatSolution_hasFDerivAt ht hg hgN x).fderiv, ← integral_sub hi hj]
  have he : (fun y : E => f y • fderiv ℝ (heatKernel t) (x-y) -
      g y • fderiv ℝ (heatKernel t) (x-y)) =
      fun y => (f y - g y) • fderiv ℝ (heatKernel t) (x-y) := by
    ext y v
    simp [sub_smul]
  rw [he]
  have hb := norm_gradient_heatSolution_le ht (hf.sub hg) hL x
  rw [(heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv] at hb
  exact hb

/-- Reversing Duhamel time keeps the gradient kernel fixed when comparing forcing times. -/
theorem duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
    fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t-s) (fun y => f (s,y)) z) x =
      ∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x := by
  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
  have he := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x)
    (a := 0) (b := t) t
  simpa only [sub_sub_cancel, sub_self, sub_zero] using he

/-- The inverse square-root majorant controls an arbitrary nonnegative time interval. -/
theorem norm_integral_inverse_sqrt_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A)
    {g : ℝ → F} (hg : ∀ r ∈ Ioo a b, ‖g r‖ ≤ A * r ^ (-(1/2 : ℝ))) :
    ‖∫ r in a..b, g r‖ ≤ 2*A*Real.sqrt (b-a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hi : IntervalIntegrable (fun r : ℝ => A * r ^ (-(1/2 : ℝ))) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))).const_mul A
  have hbound : ‖∫ r in a..b, g r‖ ≤ ∫ r in a..b, A * r ^ (-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← restrict_Ioo_eq_restrict_Ioc]
    apply MeasureTheory.norm_integral_le_of_norm_le
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hg r hr
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))] at hbound
  norm_num only [show -(1/2 : ℝ)+1 = 1/2 by norm_num] at hbound
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hbound
  have hs : Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b-a) := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 := Real.sq_sqrt (sub_nonneg.mpr hab)
    have h4 := Real.sqrt_nonneg a
    have h5 := Real.sqrt_nonneg b
    have h6 := Real.sqrt_nonneg (b-a)
    nlinarith [mul_nonneg h4 h6]
  calc
    _ ≤ A * ((Real.sqrt b - Real.sqrt a) / (1/2)) := hbound
    _ = 2*A*(Real.sqrt b - Real.sqrt a) := by ring
    _ ≤ 2*A*Real.sqrt (b-a) := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Reversed time separates a forcing increment from a short gradient tail. -/
theorem duhamel_gradient_time_holder_of_le {α T s t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t)
    (hM : 0 ≤ M) (hK : 0 ≤ K) {f : ℝ × E → ℝ}
    (hf : ContinuousOn f (cylinder T))
    (hfM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r,y)| ≤ M)
    (hfK : HasHolderBound α (cylinder T) f K) (x : E) :
    let u : ℝ → E → ℝ := fun r z =>
      ∫ v in (0 : ℝ)..r, heatSolution (r-v) (fun y => f (v,y)) z
    ‖fderiv ℝ (u t) x - fderiv ℝ (u s) x‖ ≤
      2 * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * (M+K) * (t-s)^(α/2) := by
  dsimp only
  rw [duhamel_gradient_reversed ht hf hfM, duhamel_gradient_reversed hs hf hfM]
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  let v : ℝ → ℝ → E →L[ℝ] ℝ := fun a r =>
    fderiv ℝ (heatSolution r (fun y => f (a-r,y))) x
  have hi (a : ℝ) (ha : a ∈ Icc 0 T) : IntervalIntegrable (v a) volume 0 a := by
    have h := (intervalIntegrable_gradient_heatSolution_time ha hf hfM x).comp_sub_left a
    simpa only [v, sub_zero, sub_self, sub_sub_cancel] using h.symm
  have hsub0 : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
    simpa only [uIcc_of_le hs.1, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl hst
  have hsub1 : uIcc s t ⊆ uIcc 0 t := by
    simpa only [uIcc_of_le hst, uIcc_of_le ht.1] using Icc_subset_Icc hs.1 le_rfl
  have hit0 := (hi t ht).mono_set hsub0
  have hit1 := (hi t ht).mono_set hsub1
  have hc (a : ℝ) (ha : a ∈ Icc 0 T) (r : ℝ) (hr : r ∈ Icc 0 a) :
      Continuous (fun y : E => f (a-r,y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨⟨by linarith [hr.2], by linarith [hr.1, ha.2]⟩, mem_univ y⟩)
  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
  have hb0 : ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ ≤
      2 * (K * (t-s)^(α/2) * J) * Real.sqrt s := by
    simpa only [sub_zero] using norm_integral_inverse_sqrt_le
      (a := 0) (b := s) le_rfl hs.1 (by positivity : 0 ≤ K*(t-s)^(α/2)*J)
      (g := fun r => v t r - v s r) (by
        intro r hr
        have hrt : r ∈ Icc 0 t := ⟨hr.1.le, hr.2.le.trans hst⟩
        have hrs : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
        apply gradient_heatSolution_sub_bound hr.1 (hc t ht r hrt).aestronglyMeasurable
          (hc s hs r hrs).aestronglyMeasurable
          (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y)
          (fun y => hfM (s-r) ⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩ y)
        intro y
        have h := hfK (t-r,y) ⟨⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩, mem_univ y⟩
          (s-r,y) ⟨⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩, mem_univ y⟩
        simpa [parabolicDist, sub_sub_sub_cancel_right, abs_of_nonneg (sub_nonneg.mpr hst),
          Real.sqrt_eq_rpow, ← Real.rpow_mul (sub_nonneg.mpr hst), mul_comm, div_eq_mul_inv] using h)
  have hb1 : ‖∫ r in s..t, v t r‖ ≤ 2*(M*J)*Real.sqrt (t-s) := by
    apply norm_integral_inverse_sqrt_le hs.1 hst (by positivity)
    intro r hr
    have hrt : r ∈ Icc 0 t := ⟨hs.1.trans hr.1.le, hr.2.le⟩
    exact norm_gradient_heatSolution_le (lt_of_le_of_lt hs.1 hr.1)
      (hc t ht r hrt).aestronglyMeasurable
      (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y) x
  have hδ1 : t-s ≤ 1 := by linarith [ht.2, hs.1]
  have hpow : Real.sqrt (t-s) ≤ (t-s)^(α/2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by linarith) (by linarith)
  change ‖(∫ r in (0 : ℝ)..t, v t r) - ∫ r in (0 : ℝ)..s, v s r‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hit0 hit1,
    add_sub_right_comm, ← intervalIntegral.integral_sub hit0 (hi s hs)]
  calc
    _ ≤ ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ + ‖∫ r in s..t, v t r‖ := norm_add_le _ _
    _ ≤ 2*(K*(t-s)^(α/2)*J)*Real.sqrt s + 2*(M*J)*Real.sqrt (t-s) := add_le_add hb0 hb1
    _ ≤ 2*(K*(t-s)^(α/2)*J) + 2*(M*J)*(t-s)^(α/2) :=
      add_le_add (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hs.2.trans hT1)))
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = 2*J*(M+K)*(t-s)^(α/2) := by ring

/-- Spatial interpolation and reversed-time integration give the full gradient estimate. -/
theorem duhamel_gradient_parabolic_holder :
    ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
    ContinuousOn f (cylinder T) →
    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
    HasHolderBound α (cylinder T) f K →
    HasHolderBound α (cylinder T)
      (fun p : ℝ × E => fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..p.1,
        heatSolution (p.1-s) (fun y => f (s,y)) z) p.2) (C * (M+K)) := by
  intro α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_gradient_spatial_holder α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C+2*J, by positivity, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  intro p hp q hq
  have hs := hCb T hT hT1 f M K hM hK hf hfM hspace p.1 hp.1 p.2 q.2
  have ht : ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ ≤
      2*J*(M+K)*|p.1-q.1|^(α/2) := by
    rcases le_total q.1 p.1 with hqp | hpq
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hqp)] using
        duhamel_gradient_time_holder_of_le hα hα1 hT1 hq.1 hp.1 hqp hM hK hf hfM hfK q.2
    · simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hpq), neg_sub] using
        duhamel_gradient_time_holder_of_le hα hα1 hT1 hp.1 hq.1 hpq hM hK hf hfM hfK q.2
  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htp : |p.1-q.1|^(α/2) ≤ parabolicDist p q ^ α := by
    calc
      _ = (Real.sqrt |p.1-q.1|)^α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u q.1) q.2‖ ≤
        ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u p.1) q.2‖ +
        ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ C*(M+K)*parabolicDist p q ^ α + 2*J*(M+K)*parabolicDist p q ^ α :=
      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity)))
        (ht.trans (mul_le_mul_of_nonneg_left htp (by positivity)))
    _ = (C+2*J)*(M+K)*parabolicDist p q ^ α := by ring

/-- Positive parabolic Hölder control implies continuity on the cylinder. -/
theorem continuousOn_of_hasHolderBound {F : Type*} [NormedAddCommGroup F]
    {α T K : ℝ} (hα : 0 < α) {g : ℝ × E → F}
    (hg : HasHolderBound α (cylinder T) g K) : ContinuousOn g (cylinder T) := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun q : ℝ × E => K * parabolicDist q p ^ α) := by
    dsimp [parabolicDist]
    fun_prop (disch := positivity)
  have hz : K * parabolicDist p p ^ α = 0 := by
    simp [parabolicDist, Real.zero_rpow hα.ne']
  have hlim : Filter.Tendsto (fun q => K * parabolicDist q p ^ α)
      (nhdsWithin p (cylinder T)) (nhds (K * parabolicDist p p ^ α)) :=
    hc.continuousAt.continuousWithinAt
  rw [hz] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun q => norm_nonneg (g q - g p))) _ hlim
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hg q hq p hp

set_option maxHeartbeats 800000 in
/-- The constant-coefficient Duhamel solution is bounded in the full solution graph norm. -/
theorem exists_solution_graph_bound :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1
  obtain ⟨A, hA, hAb⟩ := duhamel_hessian_bound α hα hα1
  obtain ⟨B, hB, hBb⟩ := DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian α hα hα1
  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
  obtain ⟨D, hD, hDb⟩ := duhamel_time_derivative_holder α hα hα1
  obtain ⟨V, hV, hVb⟩ := duhamel_value_time_estimates α hα hα1
  obtain ⟨W, hW, hWb⟩ := duhamel_value_parabolic_holder α hα hα1
  obtain ⟨Q, hQ, hQb⟩ := duhamel_gradient_parabolic_holder α hα hα1
  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(1+3*V)+2*W+(1+3*C)+(1+3*D)+2*J+2*Q+A+B, by positivity, ?_⟩
  intro T hT hT1 f
  let N := ‖f‖
  have hN : 0 ≤ N := norm_nonneg f
  have hfH : HasHolderBound α (cylinder T) f N := ParabolicHolder.hasHolderBound f
  have hf : ContinuousOn f (cylinder T) := continuousOn_of_hasHolderBound hα hfH
  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ N :=
    fun t _ x => ParabolicHolder.norm_le f (t,x)
  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x)-f (t,y)| ≤ N*‖x-y‖^α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using hfH (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  let v : ℝ × E → ℝ := fun p => f p + (Δ (u p.1)) p.2
  let d : ℝ × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (u p.1) p.2
  let dd : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2
  have hpow (t : ℝ) (ht : t ∈ Icc 0 T) : t^(α/2) ≤ 1 :=
    Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)
  have htime := hCb T hT hT1 f N N hN hN hf hfM hfK
  have hvalue := hVb T hT hT1 f N N hN hN hf hfM hfK
  have huB : ∀ p ∈ cylinder T, ‖u p.1 p.2‖ ≤ (1+3*V)*N := by
    intro p hp
    have hb : N+3*V*N*T^(α/2) ≤ (1+3*V)*N := by
      have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*V*N)
        (hpow T ⟨hT.le, le_rfl⟩)
      nlinarith
    exact (hvalue.1 p.1 hp.1 p.2).trans ((mul_le_mul_of_nonneg_left hb hp.1.1).trans
      (mul_le_of_le_one_left (by positivity) (hp.1.2.trans hT1)))
  have hvB : ∀ p ∈ cylinder T, ‖v p‖ ≤ (1+3*C)*N := by
    intro p hp
    have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*C*N) (hpow p.1 hp.1)
    have hb := (htime p.1 hp.1 p.2).2
    change |f p + (Δ (u p.1)) p.2| ≤ _
    nlinarith
  have hdB : ∀ p ∈ cylinder T, ‖d p‖ ≤ 2*J*N := by
    intro p hp
    have h := (duhamel_gradient_bound hp.1 hf hfM p.2).trans
      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hp.1.2.trans hT1)))
    simpa only [d, J, mul_comm, mul_left_comm, mul_assoc] using h
  have hddB : ∀ p ∈ cylinder T, ‖dd p‖ ≤ A*N := by
    intro p hp
    exact (((hAb T hT hT1 f N N hN hN hf hfM hfK).2 p.1 hp.1 p.2).2.2.2).trans
      (mul_le_of_le_one_right (by positivity) (hpow p.1 hp.1))
  have huH : HasHolderBound α (cylinder T) (fun p => u p.1 p.2) (2*W*N) := by
    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1
    ring
  have hvH : HasHolderBound α (cylinder T) v ((1+3*D)*N) := by
    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1
    ring
  have hdH : HasHolderBound α (cylinder T) d (2*Q*N) := by
    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1
    ring
  have hddH : HasHolderBound α (cylinder T) dd (B*N) := hBb T hT hT1 f N N hN hN hf hfM hfK
  have liftB {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
      (hb : ∀ p ∈ cylinder T, ‖g p‖ ≤ b) :
      ∀ p ∈ cylinder T, ‖(cylinder T).indicator g p‖ ≤ b := by
    intro p hp
    simpa only [indicator_of_mem hp] using hb p hp
  have liftH {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
      (hb : HasHolderBound α (cylinder T) g b) :
      HasHolderBound α (cylinder T) ((cylinder T).indicator g) b := by
    intro p hp q hq
    simpa only [indicator_of_mem hp, indicator_of_mem hq] using hb p hp q hq
  let iu := (cylinder T).indicator (fun p : ℝ × E => u p.1 p.2)
  let iv := (cylinder T).indicator v
  let idu := (cylinder T).indicator d
  let iddu := (cylinder T).indicator dd
  have huS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => iu (t,z)) = u t := by
    funext z
    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
  have hdS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => idu (t,z)) = fderiv ℝ (u t) := by
    funext z
    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
  have hzero : ∀ x : E, iu (0,x) = 0 := by
    intro x
    rw [show iu (0,x) = u 0 x from congrFun (huS 0 ⟨le_rfl, hT.le⟩) x]
    exact intervalIntegral.integral_same
  have hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z => iu (t,z)) (idu (t,x)) x := by
    intro t ht x
    rw [huS t ht]
    have hd0 : idu (t,x) = fderiv ℝ (u t) x := congrFun (hdS t ht) x
    rw [hd0]
    exact (hasFDerivAt_duhamel ht hf hfM x).differentiableAt.hasFDerivAt
  have hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z => idu (t,z)) (iddu (t,x)) x := by
    intro t ht x
    rw [hdS t ht]
    change HasFDerivAt (fderiv ℝ (u t)) ((cylinder T).indicator dd (t,x)) x
    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
    exact (((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
      (m := 1) (by norm_num)).differentiable_one x).hasFDerivAt
  have hut : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun s => iu (s,x)) (iv (t,x)) (Icc 0 T) t := by
    intro t ht x
    change HasDerivWithinAt _ ((cylinder T).indicator v (t,x)) _ _
    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
    exact ((htime t ht x).1).congr_of_mem (fun s hs => congrFun (huS s hs) x) ht
  let G : ParabolicSolutionGraph.Graph («E» := E) α T :=
    ParabolicSolutionGraph.ofDerivatives iu iv idu iddu
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB (fun p => u p.1 p.2) huB⟩ ⟨_, liftH (fun p => u p.1 p.2) huH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB v hvB⟩ ⟨_, liftH v hvH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB d hdB⟩ ⟨_, liftH d hdH⟩
      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB dd hddB⟩ ⟨_, liftH dd hddH⟩
      hzero hdu hddu hut
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    change (cylinder T).indicator (fun q : ℝ × E => u q.1 q.2) p = u p.1 p.2
    exact indicator_of_mem hp _
  · have huN : ‖G.u‖ ≤ (1+3*V)*N+2*W*N :=
      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB (fun p => u p.1 p.2) huB) (liftH (fun p => u p.1 p.2) huH)
    have hvN : ‖G.ut‖ ≤ (1+3*C)*N+(1+3*D)*N :=
      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB v hvB) (liftH v hvH)
    have hdN : ‖G.du‖ ≤ 2*J*N+2*Q*N :=
      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB d hdB) (liftH d hdH)
    have hddN : ‖G.ddu‖ ≤ A*N+B*N :=
      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB dd hddB) (liftH dd hddH)
    rw [ParabolicSolutionGraph.norm_eq]
    change ‖G.u‖+‖G.ut‖+‖G.du‖+‖G.ddu‖ ≤ _ * N
    nlinarith

end Poincare.DuhamelSolutionOperatorBound
