import Poincare.Global.HeatKernel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integral and convolution facts for the Euclidean heat kernel

This file proves the first fundamental-solution facts for the explicit heat
kernel from `Poincare.Global.HeatKernel`.

The total-mass theorem is stated on a general finite-dimensional real
inner-product space equipped with its Borel measurable structure and canonical
volume measure.  This is the generality supported by
`GaussianFourier.integral_rexp_neg_mul_sq_norm`.

For convolution against initial data, the first API-supported class is bounded
continuous real-valued data: the kernel is integrable, so the convolution
integrand is dominated by the kernel times a uniform bound for the data.

The final theorem records the approximate-identity convergence reached directly
by Mathlib's Fourier inversion machinery, after the heat-time scale change
`c = (4π²t)⁻¹`.  It is intentionally kept in Mathlib's complex,
Fourier-normalized Gaussian form rather than pretending the remaining
`cpow`/`rpow` coercion algebra has already identified it with `heatSolution`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Convolution Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma integrable_exp_neg_one_div_four_mul_norm_sq {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2)) := by
  have hcomplex :
      Integrable
        (fun x : E => Complex.exp (-(1 / (4 * t) : ℂ) * (‖x‖ ^ 2 : ℂ))) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (1 / (4 * t) : ℂ)) (c := 0) (w := (0 : E)) (by
        simp [ht])
  convert hcomplex.re using 2 with x
  rw [← Complex.exp_ofReal_re (-(1 / (4 * t)) * ‖x‖ ^ 2)]
  congr 1
  push_cast
  ring

/-- For positive time, the heat kernel is integrable over the model space. -/
theorem heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => heatKernel (E := E) t x) := by
  have hg := integrable_exp_neg_one_div_four_mul_norm_sq (E := E) ht
  unfold heatKernel
  convert hg.const_mul ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)) using 2 with x
  ring_nf

/-- The positive-time heat kernel has total mass one. -/
theorem integral_heatKernel_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x : E, heatKernel (E := E) t x = 1 := by
  have hbase : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hgauss :
      ∫ x : E, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) =
        (Real.pi / (1 / (4 * t))) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    exact GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1 / (4 * t))
      (by positivity)
  have hfun : ∀ x : E,
      Real.exp (-(‖x‖ ^ 2) / (4 * t)) =
        Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    intro x
    congr 1
    field_simp [ht.ne']
  unfold heatKernel
  simp_rw [hfun]
  rw [integral_const_mul, hgauss]
  have hscale : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
    field_simp [ht.ne']
  rw [hscale]
  rw [← Real.rpow_add hbase]
  ring_nf
  simp

/-- Heat evolution as convolution with the positive-time heat kernel. -/
def heatSolution (t : ℝ) (f : E → ℝ) : E → ℝ :=
  MeasureTheory.convolution (fun x : E => heatKernel (E := E) t x) f
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The defining integral formula for `heatSolution`. -/
@[simp]
theorem heatSolution_apply (t : ℝ) (f : E → ℝ) (x : E) :
    heatSolution (E := E) t f x =
      ∫ y : E, heatKernel (E := E) t y * f (x - y) := by
  simp [heatSolution, MeasureTheory.convolution_lsmul, smul_eq_mul]

/--
The heat-kernel convolution integrand is integrable at every point for bounded
continuous real-valued initial data.
-/
theorem heatKernel_convolutionExistsAt_of_bounded_continuous {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ConvolutionExistsAt (fun y : E => heatKernel (E := E) t y) f x
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  rw [ConvolutionExistsAt]
  have hshift_meas : AEStronglyMeasurable (fun y : E => f (x - y)) volume := by
    exact (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hshift_mem : MemLp (fun y : E => f (x - y)) ⊤ volume := by
    exact memLp_top_of_bound hshift_meas C
      (Filter.Eventually.of_forall fun y => hC (x - y))
  exact (heatKernel_integrable (E := E) ht).smul_of_top_left hshift_mem

/-- The heat-kernel convolution exists everywhere for bounded continuous data. -/
theorem heatKernel_convolutionExists_of_bounded_continuous {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ConvolutionExists (fun y : E => heatKernel (E := E) t y) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  intro x
  exact heatKernel_convolutionExistsAt_of_bounded_continuous (E := E) ht hf hC x

/--
Convolution with the positive-time heat kernel is continuous for bounded
continuous real-valued initial data.
-/
theorem continuous_heatSolution_of_bounded_continuous {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : Continuous f)
    (hfb : BddAbove (Set.range fun x => ‖f x‖)) :
    Continuous (heatSolution (E := E) t f) := by
  unfold heatSolution
  exact hfb.continuous_convolution_right_of_integrable (ContinuousLinearMap.lsmul ℝ ℝ)
    (heatKernel_integrable (E := E) ht) hf

private lemma heatTimeFourierScale_tendsto_atTop :
    Tendsto (fun t : ℝ => ((4 * Real.pi ^ 2) * t)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
  have hmul_nhds :
      Tendsto (fun t : ℝ => (4 * Real.pi ^ 2) * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (4 * Real.pi ^ 2)
      (Filter.tendsto_id.mono_right nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0)))
  have hmul_pos :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (4 * Real.pi ^ 2) * t ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_mem_nhdsWithin] with t (ht : t ∈ Set.Ioi (0 : ℝ))
    exact Set.mem_Ioi.mpr (mul_pos (by positivity) (Set.mem_Ioi.mp ht))
  have hmul_gt :
      Tendsto (fun t : ℝ => (4 * Real.pi ^ 2) * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hmul_nhds, hmul_pos⟩
  exact hmul_gt.inv_tendsto_nhdsGT_zero

/--
Approximate-identity convergence in Mathlib's Fourier-normalized complex
Gaussian form, composed with the heat-time scale `c = (4π²t)⁻¹`.

This is the verified initial-data recovery seed currently available from the
pinned Mathlib API.  The real `heatSolution t f` statement needs the remaining
identification of this complex `cpow` normalization with the real `rpow`
normalization in `heatKernel`.
-/
theorem gaussianApproxIdentity_heatTimeScale_complex {f : E → ℂ} (hf : Integrable f)
    {x : E} (hcf : ContinuousAt f x) :
    Tendsto
      (fun t : ℝ =>
        ∫ y : E,
          (((Real.pi : ℂ) * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ)) ^
                ((Module.finrank ℝ E : ℂ) / 2) *
              Complex.exp
                (-(Real.pi : ℂ) ^ 2 * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ) *
                  (‖x - y‖ ^ 2 : ℂ))) •
            f y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  simpa only [Function.comp_apply] using
    (Real.tendsto_integral_gaussian_smul' (V := E) hf hcf).comp
      heatTimeFourierScale_tendsto_atTop

end Poincare
