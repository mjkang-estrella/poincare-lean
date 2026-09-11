import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

end Poincare.HeatDuhamelHeatEquation
