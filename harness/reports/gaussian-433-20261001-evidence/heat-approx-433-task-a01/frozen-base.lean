import Poincare.Global.HeatKernelIntegral

/-!
# Heat-kernel approximate identity

This file closes the bridge left by `Poincare.Global.HeatKernelIntegral`: the
Fourier-normalized complex Gaussian at heat scale is identified with the real
heat kernel, then Mathlib's complex approximate-identity theorem is converted
back to the real `heatSolution`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Convolution Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma heatKernel_fourier_prefactor_real {t : ℝ} (ht : 0 < t) :
    (Real.pi * (((4 * Real.pi ^ 2) * t)⁻¹)) ^ ((Module.finrank ℝ E : ℝ) / 2) =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  have hscale : Real.pi * (((4 * Real.pi ^ 2) * t)⁻¹) = (4 * Real.pi * t)⁻¹ := by
    field_simp [Real.pi_ne_zero, ht.ne']
  rw [hscale]
  simpa [neg_div] using
    (Real.rpow_neg_eq_inv_rpow (4 * Real.pi * t) ((Module.finrank ℝ E : ℝ) / 2)).symm

omit [InnerProductSpace ℝ E] in
private lemma heatKernel_fourier_exponent_real {t : ℝ} (ht : 0 < t) (z : E) :
    -(Real.pi ^ 2) * (((4 * Real.pi ^ 2) * t)⁻¹) * ‖z‖ ^ 2 =
      -(‖z‖ ^ 2) / (4 * t) := by
  field_simp [Real.pi_ne_zero, ht.ne']

variable [FiniteDimensional ℝ E]

/--
The Fourier-normalized complex Gaussian at heat scale is exactly the
complexification of the real heat kernel.

The half-dimensional normalization is handled through `Real.rpow` after
rewriting the positive complex `cpow` base as a real coercion.
-/
theorem heatKernel_fourier_complex_eq_ofReal {t : ℝ} (ht : 0 < t) (x y : E) :
    (((Real.pi : ℂ) * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ)) ^
          ((Module.finrank ℝ E : ℂ) / 2) *
        Complex.exp
          (-(Real.pi : ℂ) ^ 2 * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ) *
            (‖x - y‖ ^ 2 : ℂ))) =
      (heatKernel (E := E) t (x - y) : ℂ) := by
  have hpref_nonneg : 0 ≤ Real.pi * (((4 * Real.pi ^ 2) * t)⁻¹) := by
    positivity
  have hfin : ((Module.finrank ℝ E : ℂ) / 2) =
      (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_div]
  have harg :
      -(Real.pi : ℂ) ^ 2 * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ) *
          (‖x - y‖ ^ 2 : ℂ) =
        ((-(Real.pi ^ 2) * (((4 * Real.pi ^ 2) * t)⁻¹) * ‖x - y‖ ^ 2 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
  rw [hfin]
  rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_cpow hpref_nonneg ((Module.finrank ℝ E : ℝ) / 2)]
  rw [harg, ← Complex.ofReal_exp]
  unfold heatKernel
  rw [← Complex.ofReal_mul]
  rw [Complex.ofReal_inj]
  rw [heatKernel_fourier_prefactor_real (E := E) ht,
    heatKernel_fourier_exponent_real (E := E) ht (x - y)]

variable [MeasurableSpace E] [BorelSpace E]

/-- Symmetric `x - y` form of `heatSolution`, matching Mathlib's Gaussian approximate identity. -/
theorem heatSolution_apply_swap (t : ℝ) (f : E → ℝ) (x : E) :
    heatSolution (E := E) t f x = ∫ y : E, heatKernel (E := E) t (x - y) * f y := by
  unfold heatSolution
  simpa [smul_eq_mul] using
    (MeasureTheory.convolution_lsmul_swap (μ := volume)
      (f := fun z : E => heatKernel (E := E) t z) (g := f) (x := x))

private lemma gaussian_heat_integral_eq_heatSolution_of_pos {t : ℝ} (ht : 0 < t)
    (f : E → ℝ) (x : E) :
    (∫ y : E,
      (((Real.pi : ℂ) * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ)) ^
            ((Module.finrank ℝ E : ℂ) / 2) *
          Complex.exp
            (-(Real.pi : ℂ) ^ 2 * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ) *
              (‖x - y‖ ^ 2 : ℂ))) •
        (f y : ℂ)) =
      (heatSolution (E := E) t f x : ℂ) := by
  rw [integral_congr_ae (Eventually.of_forall fun y => by
    rw [heatKernel_fourier_complex_eq_ofReal (E := E) ht x y])]
  simp_rw [smul_eq_mul, ← Complex.ofReal_mul]
  norm_cast
  exact (heatSolution_apply_swap (E := E) t f x).symm

/--
Heat-kernel convolution recovers integrable real initial data at continuity
points as `t → 0+`.

This is the real-valued consequence of Mathlib's complex Fourier-normalized
Gaussian approximate identity, using `heatKernel_fourier_complex_eq_ofReal`.
-/
theorem tendsto_heatSolution_nhdsGT_zero {f : E → ℝ} (hf : Integrable f)
    {x : E} (hcf : ContinuousAt f x) :
    Tendsto (fun t : ℝ => heatSolution (E := E) t f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  let fC : E → ℂ := fun y => (f y : ℂ)
  have hseed :
      Tendsto
        (fun t : ℝ =>
          ∫ y : E,
            (((Real.pi : ℂ) * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ)) ^
                  ((Module.finrank ℝ E : ℂ) / 2) *
                Complex.exp
                  (-(Real.pi : ℂ) ^ 2 * ((((4 * Real.pi ^ 2) * t)⁻¹ : ℝ) : ℂ) *
                    (‖x - y‖ ^ 2 : ℂ))) •
              fC y)
        (𝓝[>] (0 : ℝ)) (𝓝 (fC x)) := by
    exact gaussianApproxIdentity_heatTimeScale_complex (E := E) (f := fC) hf.ofReal
      (Complex.continuous_ofReal.continuousAt.comp hcf)
  have hcomplex :
      Tendsto (fun t : ℝ => (heatSolution (E := E) t f x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((f x : ℝ) : ℂ)) := by
    refine hseed.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t (ht : t ∈ Set.Ioi (0 : ℝ))
    exact gaussian_heat_integral_eq_heatSolution_of_pos (E := E) (Set.mem_Ioi.mp ht) f x
  have hreal := (Complex.continuous_re.tendsto ((f x : ℝ) : ℂ)).comp hcomplex
  simpa using hreal

end Poincare
