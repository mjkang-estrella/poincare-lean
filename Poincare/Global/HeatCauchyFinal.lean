import Poincare.Global.HeatEnvelopes
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Final heat-kernel Cauchy estimates

This module closes the pointwise domination estimates needed by the heat Cauchy
interface.  The time derivative is first factored into the heat kernel times a
quadratic scalar; the compact time-window estimate then compares the Gaussian
at time `τ ∈ [t/2, 2*t]` to the fixed heat kernel at time `2*t`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Reverse translated quadratic control, matching the envelope polynomial. -/
theorem one_add_norm_sq_sub_left_le_translate_bound (x y : E) :
    1 + ‖x - y‖ ^ 2 ≤ (3 + 2 * ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
  simpa [sub_sub_cancel] using
    (one_add_norm_sq_le_translate_bound (E := E) x (x - y))

/-- The time derivative of the heat kernel in factored scalar form. -/
theorem deriv_heatKernel_time_eq_heatKernel_mul {t : ℝ} (ht : 0 < t) (u : E) :
    deriv (fun τ : ℝ => heatKernel (E := E) τ u) t =
      heatKernel (E := E) t u *
        (‖u‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) := by
  rw [deriv_heatKernel_time (E := E) ht u]
  unfold heatKernel
  have hbase_pos : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  rw [Real.rpow_sub_one hbase_pos.ne' (-(Module.finrank ℝ E : ℝ) / 2)]
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

/-- The translated spatial Laplacian in the same factored scalar form. -/
theorem laplacian_heatKernel_sub_left_eq_heatKernel_mul {t : ℝ} (ht : 0 < t) (x y : E) :
    (Δ fun z : E => heatKernel (E := E) t (z - y)) x =
      heatKernel (E := E) t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) := by
  rw [← heatKernel_sub_left_heatEquation_laplacian (E := E) ht x y]
  exact deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht (x - y)

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- Uniform Gaussian-normalization ratio for `τ ∈ [t/2, 2*t]`. -/
def heatKernelTimeWindowGaussianRatio (t : ℝ) : ℝ :=
  (4 * Real.pi * (t / 2)) ^ (-(Module.finrank ℝ E : ℝ) / 2) /
    (4 * Real.pi * (2 * t)) ^ (-(Module.finrank ℝ E : ℝ) / 2)

/-- Constant for the time-window derivative domination envelope. -/
def heatKernelTimeWindowDominationConstant (t C : ℝ) (x : E) : ℝ :=
  C * heatKernelTimeWindowGaussianRatio (E := E) t *
    ((1 / t ^ 2 + (Module.finrank ℝ E : ℝ) / t) * (3 + 2 * ‖x‖ ^ 2))

/-- Constant for the fixed-time Laplacian domination envelope. -/
def heatKernelLaplacianDominationConstant (t C : ℝ) (x : E) : ℝ :=
  C * ((1 / (4 * t ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * t)|) *
    (3 + 2 * ‖x‖ ^ 2))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Heat kernels in the compact time window are dominated by the fixed `2*t` heat kernel. -/
theorem heatKernel_time_window_gaussian_le {t τ : ℝ} (ht : 0 < t)
    (hτ : τ ∈ Set.Icc (t / 2) (2 * t)) (u : E) :
    heatKernel (E := E) τ u ≤
      heatKernelTimeWindowGaussianRatio (E := E) t * heatKernel (E := E) (2 * t) u := by
  unfold heatKernel heatKernelTimeWindowGaussianRatio
  set p : ℝ := -(Module.finrank ℝ E : ℝ) / 2
  set r2 : ℝ := ‖u‖ ^ 2
  have hτ_pos : 0 < τ := (half_pos ht).trans_le hτ.1
  have hlow_pos : 0 < 4 * Real.pi * (t / 2) := by positivity
  have hτbase_pos : 0 < 4 * Real.pi * τ := by positivity
  have htwobase_pos : 0 < 4 * Real.pi * (2 * t) := by positivity
  have hn_nonneg : 0 ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.zero_le (Module.finrank ℝ E)
  have hp_nonpos : p ≤ 0 := by
    dsimp [p]
    nlinarith [hn_nonneg]
  have hlow_le_base : 4 * Real.pi * (t / 2) ≤ 4 * Real.pi * τ := by
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos, hτ.1]
  have hnorm_le : (4 * Real.pi * τ) ^ p ≤ (4 * Real.pi * (t / 2)) ^ p :=
    Real.rpow_le_rpow_of_nonpos hlow_pos hlow_le_base hp_nonpos
  have hden_le : 4 * τ ≤ 4 * (2 * t) := by nlinarith [hτ.2]
  have hden_pos : 0 < 4 * τ := by positivity
  have hdiv : r2 / (4 * (2 * t)) ≤ r2 / (4 * τ) := by
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hexp_arg : -r2 / (4 * τ) ≤ -r2 / (4 * (2 * t)) := by
    have h := neg_le_neg hdiv
    convert h using 1 <;> ring
  have hexp_le : Real.exp (-r2 / (4 * τ)) ≤ Real.exp (-r2 / (4 * (2 * t))) :=
    Real.exp_le_exp.mpr hexp_arg
  have hlow_rpow_nonneg : 0 ≤ (4 * Real.pi * (t / 2)) ^ p :=
    (Real.rpow_pos_of_pos hlow_pos p).le
  have hmul_le :
      (4 * Real.pi * τ) ^ p * Real.exp (-r2 / (4 * τ)) ≤
        (4 * Real.pi * (t / 2)) ^ p * Real.exp (-r2 / (4 * (2 * t))) := by
    exact mul_le_mul hnorm_le hexp_le (Real.exp_pos _).le hlow_rpow_nonneg
  have hden_ne : (4 * Real.pi * (2 * t)) ^ p ≠ 0 :=
    (Real.rpow_pos_of_pos htwobase_pos p).ne'
  calc
    (4 * Real.pi * τ) ^ p * Real.exp (-‖u‖ ^ 2 / (4 * τ)) =
        (4 * Real.pi * τ) ^ p * Real.exp (-r2 / (4 * τ)) := by simp [r2]
    _ ≤ (4 * Real.pi * (t / 2)) ^ p * Real.exp (-r2 / (4 * (2 * t))) := hmul_le
    _ = ((4 * Real.pi * (t / 2)) ^ p / (4 * Real.pi * (2 * t)) ^ p) *
        ((4 * Real.pi * (2 * t)) ^ p * Real.exp (-r2 / (4 * (2 * t)))) := by
      field_simp [hden_ne]
    _ = ((4 * Real.pi * (t / 2)) ^ p / (4 * Real.pi * (2 * t)) ^ p) *
        ((4 * Real.pi * (2 * t)) ^ p * Real.exp (-‖u‖ ^ 2 / (4 * (2 * t)))) := by
          simp [r2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Fixed-time quadratic factor bounded by the Laplacian envelope polynomial. -/
theorem heatKernel_laplacian_quadratic_abs_le {t : ℝ} (ht : 0 < t) (x y : E) :
    |‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)| ≤
      ((1 / (4 * t ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * t)|) *
        (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2) := by
  set r2 : ℝ := ‖x - y‖ ^ 2
  set b : ℝ := (Module.finrank ℝ E : ℝ) / (2 * t)
  set K : ℝ := 3 + 2 * ‖x‖ ^ 2
  set P : ℝ := 1 + ‖y‖ ^ 2
  have hr2_nonneg : 0 ≤ r2 := by simp [r2]
  have hcoeff_nonneg : 0 ≤ 1 / (4 * t ^ 2) := by positivity
  have hK_nonneg : 0 ≤ K := by nlinarith [sq_nonneg ‖x‖]
  have hP_nonneg : 0 ≤ P := by nlinarith [sq_nonneg ‖y‖]
  have hK_ge_one : 1 ≤ K := by nlinarith [sq_nonneg ‖x‖]
  have hP_ge_one : 1 ≤ P := by nlinarith [sq_nonneg ‖y‖]
  have hKP_ge_one : 1 ≤ K * P := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ K * P := mul_le_mul hK_ge_one hP_ge_one zero_le_one hK_nonneg
  have hr2_le : r2 ≤ K * P := by
    have h := one_add_norm_sq_sub_left_le_translate_bound (E := E) x y
    nlinarith [h, hr2_nonneg]
  have hterm1 : r2 / (4 * t ^ 2) ≤ (1 / (4 * t ^ 2)) * (K * P) := by
    calc
      r2 / (4 * t ^ 2) = (1 / (4 * t ^ 2)) * r2 := by ring
      _ ≤ (1 / (4 * t ^ 2)) * (K * P) :=
        mul_le_mul_of_nonneg_left hr2_le hcoeff_nonneg
  have hterm2 : |b| ≤ |b| * (K * P) :=
    le_mul_of_one_le_right (abs_nonneg b) hKP_ge_one
  have hterm_nonneg : 0 ≤ r2 / (4 * t ^ 2) := by positivity
  have habs : |r2 / (4 * t ^ 2) - b| ≤ r2 / (4 * t ^ 2) + |b| := by
    have h := abs_add_le (r2 / (4 * t ^ 2)) (-b)
    simpa [sub_eq_add_neg, abs_of_nonneg hterm_nonneg] using h
  calc
    |‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)| =
        |r2 / (4 * t ^ 2) - b| := by simp [r2, b]
    _ ≤ r2 / (4 * t ^ 2) + |b| := habs
    _ ≤ (1 / (4 * t ^ 2)) * (K * P) + |b| * (K * P) :=
      add_le_add hterm1 hterm2
    _ = ((1 / (4 * t ^ 2) + |b|) * K) * P := by ring
    _ = ((1 / (4 * t ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * t)|) *
        (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2) := by simp [K, P, b]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Time-window quadratic factor bounded uniformly over `τ ∈ [t/2, 2*t]`. -/
theorem heatKernel_time_window_quadratic_abs_le {t τ : ℝ} (ht : 0 < t)
    (hτ : τ ∈ Set.Icc (t / 2) (2 * t)) (x y : E) :
    |‖x - y‖ ^ 2 / (4 * τ ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * τ)| ≤
      ((1 / t ^ 2 + (Module.finrank ℝ E : ℝ) / t) *
        (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2) := by
  have hτ_pos : 0 < τ := (half_pos ht).trans_le hτ.1
  have hfixed := heatKernel_laplacian_quadratic_abs_le (E := E) hτ_pos x y
  set K : ℝ := 3 + 2 * ‖x‖ ^ 2
  set P : ℝ := 1 + ‖y‖ ^ 2
  have hK_nonneg : 0 ≤ K := by nlinarith [sq_nonneg ‖x‖]
  have hP_nonneg : 0 ≤ P := by nlinarith [sq_nonneg ‖y‖]
  have ht_le_twoτ : t ≤ 2 * τ := by nlinarith [hτ.1]
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos ht
  have hsq : t ^ 2 ≤ (2 * τ) ^ 2 := pow_le_pow_left₀ ht.le ht_le_twoτ 2
  have hsq' : t ^ 2 ≤ 4 * τ ^ 2 := by nlinarith [hsq]
  have hcoef1 : 1 / (4 * τ ^ 2) ≤ 1 / t ^ 2 :=
    div_le_div_of_nonneg_left zero_le_one ht_sq_pos hsq'
  have hn_nonneg : 0 ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.zero_le (Module.finrank ℝ E)
  have hcoef2 : (Module.finrank ℝ E : ℝ) / (2 * τ) ≤
      (Module.finrank ℝ E : ℝ) / t :=
    div_le_div_of_nonneg_left hn_nonneg ht ht_le_twoτ
  have hcoef2_nonneg : 0 ≤ (Module.finrank ℝ E : ℝ) / (2 * τ) := by positivity
  have hcoef_le :
      1 / (4 * τ ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * τ)| ≤
        1 / t ^ 2 + (Module.finrank ℝ E : ℝ) / t := by
    rw [abs_of_nonneg hcoef2_nonneg]
    exact add_le_add hcoef1 hcoef2
  have hmul :
      ((1 / (4 * τ ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * τ)|) * K) * P ≤
        ((1 / t ^ 2 + (Module.finrank ℝ E : ℝ) / t) * K) * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef_le hK_nonneg) hP_nonneg
  exact hfixed.trans (by simpa [K, P] using hmul)

omit [MeasurableSpace E] [BorelSpace E] in
/--
Pointwise domination of the time-derivative integrand by the fixed
`heatKernelTimeWindowEnvelope`.
-/
theorem heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope {t τ C : ℝ}
    (ht : 0 < t) (hτ : τ ∈ Set.Icc (t / 2) (2 * t))
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤
      heatKernelTimeWindowEnvelope (E := E) t
        (heatKernelTimeWindowDominationConstant (E := E) t C x) x y := by
  have hτ_pos : 0 < τ := (half_pos ht).trans_le hτ.1
  rw [deriv_heatKernel_time_eq_heatKernel_mul (E := E) hτ_pos (x - y)]
  set hkτ : ℝ := heatKernel (E := E) τ (x - y)
  set hk2 : ℝ := heatKernel (E := E) (2 * t) (x - y)
  set q : ℝ := ‖x - y‖ ^ 2 / (4 * τ ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * τ)
  set R : ℝ := heatKernelTimeWindowGaussianRatio (E := E) t
  set B : ℝ := ((1 / t ^ 2 + (Module.finrank ℝ E : ℝ) / t) *
    (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2)
  have hkτ_nonneg : 0 ≤ hkτ := heatKernel_nonneg (E := E) hτ_pos (x - y)
  have hk2_nonneg : 0 ≤ hk2 := heatKernel_nonneg (E := E) (by positivity) (x - y)
  have hR_nonneg : 0 ≤ R := by
    unfold R heatKernelTimeWindowGaussianRatio
    positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hkg : hkτ ≤ R * hk2 := by
    simpa [hkτ, hk2, R] using heatKernel_time_window_gaussian_le (E := E) ht hτ (x - y)
  have hq : |q| ≤ B := by
    simpa [q, B] using heatKernel_time_window_quadratic_abs_le (E := E) ht hτ x y
  have hnorm_eq : ‖(hkτ * q) * f y‖ = hkτ * |q| * ‖f y‖ := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hkτ_nonneg, Real.norm_eq_abs]
  have hRh_nonneg : 0 ≤ R * hk2 := mul_nonneg hR_nonneg hk2_nonneg
  have hmain_nonneg : 0 ≤ (R * hk2) * B := mul_nonneg hRh_nonneg hB_nonneg
  calc
    ‖(hkτ * q) * f y‖ = hkτ * |q| * ‖f y‖ := hnorm_eq
    _ ≤ (R * hk2) * |q| * ‖f y‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkg (abs_nonneg q)) (norm_nonneg (f y))
    _ ≤ (R * hk2) * B * ‖f y‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq hRh_nonneg) (norm_nonneg (f y))
    _ ≤ (R * hk2) * B * C := by
      exact mul_le_mul_of_nonneg_left (hC y) hmain_nonneg
    _ = heatKernelTimeWindowEnvelope (E := E) t
        (heatKernelTimeWindowDominationConstant (E := E) t C x) x y := by
      simp [heatKernelTimeWindowEnvelope, heatKernelGaussianPolynomialEnvelope,
        heatKernelTimeWindowDominationConstant, hk2, R, B]
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/--
Pointwise domination of the translated spatial Laplacian integrand by the
fixed-time Laplacian envelope.
-/
theorem laplacian_heatKernel_sub_left_mul_le_laplacianEnvelope {t C : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖(Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y‖ ≤
      heatKernelLaplacianEnvelope (E := E) t
        (heatKernelLaplacianDominationConstant (E := E) t C x) x y := by
  rw [laplacian_heatKernel_sub_left_eq_heatKernel_mul (E := E) ht x y]
  set hk : ℝ := heatKernel (E := E) t (x - y)
  set q : ℝ := ‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)
  set B : ℝ := ((1 / (4 * t ^ 2) + |(Module.finrank ℝ E : ℝ) / (2 * t)|) *
    (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2)
  have hk_nonneg : 0 ≤ hk := heatKernel_nonneg (E := E) ht (x - y)
  have hB_nonneg : 0 ≤ B := by positivity
  have hq : |q| ≤ B := by
    simpa [q, B] using heatKernel_laplacian_quadratic_abs_le (E := E) ht x y
  have hnorm_eq : ‖(hk * q) * f y‖ = hk * |q| * ‖f y‖ := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, Real.norm_eq_abs]
  calc
    ‖(hk * q) * f y‖ = hk * |q| * ‖f y‖ := hnorm_eq
    _ ≤ hk * B * ‖f y‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq hk_nonneg) (norm_nonneg (f y))
    _ ≤ hk * B * C := by
      exact mul_le_mul_of_nonneg_left (hC y) (mul_nonneg hk_nonneg hB_nonneg)
    _ = heatKernelLaplacianEnvelope (E := E) t
        (heatKernelLaplacianDominationConstant (E := E) t C x) x y := by
      simp [heatKernelLaplacianEnvelope, heatKernelGaussianPolynomialEnvelope,
        heatKernelLaplacianDominationConstant, hk, B]
      ring

/-- Measurability of the time-derivative integrand in the convolution variable. -/
theorem heatKernel_time_deriv_integrand_aestronglyMeasurable {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (x : E) :
    AEStronglyMeasurable
      (fun y : E => deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) volume := by
  have hsub : Continuous fun y : E => x - y := continuous_const.sub continuous_id
  have hk : Continuous fun y : E => heatKernel (E := E) t (x - y) :=
    (contDiff_heatKernel_spatial (E := E) t).continuous.comp hsub
  have hq : Continuous fun y : E =>
      ‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t) := by
    fun_prop
  have hcont : Continuous fun y : E =>
      heatKernel (E := E) t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) :=
    hk.mul hq
  have hmeas := hcont.aestronglyMeasurable.mul hf
  convert hmeas using 1
  ext y
  rw [deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht (x - y)]
  rfl

/--
Time differentiation under the heat-kernel convolution integral, discharged by
the fixed time-window envelope above.
-/
theorem heatKernel_time_deriv_integral_hasDerivAt {t C : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hC : ∀ y, ‖f y‖ ≤ C) (x : E) :
    HasDerivAt
      (fun τ : ℝ => ∫ y : E, heatKernel (E := E) τ (x - y) * f y)
      (∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) t := by
  let bound : E → ℝ := fun y => heatKernelTimeWindowEnvelope (E := E) t
    (heatKernelTimeWindowDominationConstant (E := E) t C x) x y
  let s : Set ℝ := Set.Ioo (t / 2) (2 * t)
  have hs : s ∈ 𝓝 t := by
    refine Ioo_mem_nhds ?_ ?_ <;> linarith
  have hF_meas : ∀ᶠ τ in 𝓝 t,
      AEStronglyMeasurable (fun y : E => heatKernel (E := E) τ (x - y) * f y) volume := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have hsub : Continuous fun y : E => x - y := continuous_const.sub continuous_id
    have hk : Continuous fun y : E => heatKernel (E := E) τ (x - y) :=
      (contDiff_heatKernel_spatial (E := E) τ).continuous.comp hsub
    exact hk.aestronglyMeasurable.mul hf
  have hF_int : Integrable (fun y : E => heatKernel (E := E) t (x - y) * f y) volume :=
    (heatKernel_bounded_data_domination (E := E) ht hf hC x).2.2
  have hF'_meas : AEStronglyMeasurable
      (fun y : E => deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) volume :=
    heatKernel_time_deriv_integrand_aestronglyMeasurable (E := E) ht hf x
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ τ ∈ s,
      ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall ?_
    intro y τ hτs
    have hτIcc : τ ∈ Set.Icc (t / 2) (2 * t) :=
      ⟨le_of_lt hτs.1, le_of_lt hτs.2⟩
    exact heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope
      (E := E) ht hτIcc hC x y
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact integrable_heatKernelTimeWindowEnvelope (E := E) ht
      (heatKernelTimeWindowDominationConstant (E := E) t C x) x
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ τ ∈ s,
      HasDerivAt (fun τ : ℝ => heatKernel (E := E) τ (x - y) * f y)
        (deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y) τ := by
    refine Filter.Eventually.of_forall ?_
    intro y τ hτs
    have hτIcc : τ ∈ Set.Icc (t / 2) (2 * t) :=
      ⟨le_of_lt hτs.1, le_of_lt hτs.2⟩
    have hτ_pos : 0 < τ := heatKernel_time_window_pos ht hτIcc
    have hbase := hasDerivAt_heatKernel_time (E := E) hτ_pos (x - y)
    simpa [deriv_heatKernel_time (E := E) hτ_pos (x - y)] using hbase.mul_const (f y)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ y => heatKernel (E := E) τ (x - y) * f y)
    (F' := fun τ y => deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y)
    (x₀ := t) (s := s) (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/--
Heat equation with the time interchange discharged.  The only remaining
hypothesis is the spatial Laplacian interchange.
-/
theorem heatSolution_solves_heatEquation_of_spatial_interchange {t C : ℝ}
    (ht : 0 < t) {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
    (hC : ∀ y, ‖f y‖ ≤ C) {x : E}
    (hlap :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
      (Δ fun z : E => heatSolution (E := E) t f z) x := by
  exact heatSolution_solves_heatEquation_of_differentiation_under_integral (E := E) ht
    (heatKernel_time_deriv_integral_hasDerivAt (E := E) ht hf hC x) hlap

/--
Model Cauchy theorem with the time interchange discharged.  The remaining
hypothesis is exactly the spatial Laplacian interchange.
-/
theorem heatSolution_model_cauchy_problem_of_spatial_interchange {t C : ℝ}
    (ht : 0 < t) {f : E → ℝ} (hf : Integrable f) (hC : ∀ y, ‖f y‖ ≤ C)
    {x : E} (hcf : ContinuousAt f x)
    (hlap :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
        (Δ fun z : E => heatSolution (E := E) t f z) x ∧
      Tendsto (fun τ : ℝ => heatSolution (E := E) τ f x)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  exact heatSolution_model_cauchy_problem_of_differentiation_under_integral (E := E)
    ht hf hcf
    (heatKernel_time_deriv_integral_hasDerivAt (E := E) ht hf.aestronglyMeasurable hC x) hlap

end Measurable

end Poincare
