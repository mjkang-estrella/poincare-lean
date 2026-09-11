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

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

end Poincare.HeatDuhamelHeatEquation
