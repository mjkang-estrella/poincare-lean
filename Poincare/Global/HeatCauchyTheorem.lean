import Poincare.Global.HeatCauchyFinal

/-!
# Heat-kernel Cauchy theorem

This file is the M2-heat-10 work surface.  It starts with the missing
first-spatial-derivative domination layer needed for the directional
two-step Laplacian interchange.
-/

noncomputable section

open MeasureTheory Filter
open ContinuousLinearMap (toSpanSingleton)
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A norm is controlled by the quadratic polynomial used in the heat envelopes. -/
theorem norm_sub_left_le_translate_bound (x y : E) :
    ‖x - y‖ ≤ (3 + 2 * ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
  have hnorm_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hnorm_le_one_add : ‖x - y‖ ≤ 1 + ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - y‖ - 1)]
  exact hnorm_le_one_add.trans (one_add_norm_sq_sub_left_le_translate_bound (E := E) x y)

/-- Spatial Fréchet derivative of the heat kernel. -/
theorem hasFDerivAt_heatKernel_spatial {t : ℝ} (ht : t ≠ 0) (u : E) :
    HasFDerivAt (fun z : E => heatKernel (E := E) t z)
      (((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)) •
        (Real.exp (-(‖u‖ ^ 2) / (4 * t)) •
          ((-(1 / (2 * t))) • (innerSL ℝ u)))) u := by
  simpa [heatKernel] using
    (hasFDerivAt_exp_neg_norm_sq_div (E := E) t ht u).const_mul
      ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2))

/-- Spatial line derivative of the heat kernel in direction `v`. -/
theorem hasDerivAt_heatKernel_spatial_line {t : ℝ} (ht : t ≠ 0)
    (x y v : E) (r : ℝ) :
    HasDerivAt (fun ρ : ℝ => heatKernel (E := E) t (x + ρ • v - y))
      (heatKernel (E := E) t (x + r • v - y) *
        (-(⟪x + r • v - y, v⟫_ℝ / (2 * t)))) r := by
  let u : E := x + r • v - y
  have hline_smul : HasDerivAt (fun ρ : ℝ => ρ • v) v r := by
    simpa [toSpanSingleton_apply_one] using (toSpanSingleton ℝ v).hasDerivAt r
  have hline : HasDerivAt (fun ρ : ℝ => x + ρ • v - y) v r :=
    (hline_smul.const_add x).sub_const y
  have hcomp :=
    (hasFDerivAt_heatKernel_spatial (E := E) ht u).comp_hasDerivAt r hline
  convert hcomp using 1
  · simp [u]
  · simp [u, heatKernel, innerSL_apply, smul_eq_mul]
    ring

/-- Derivative form of `hasDerivAt_heatKernel_spatial_line`. -/
theorem deriv_heatKernel_spatial_line {t : ℝ} (ht : t ≠ 0) (x y v : E) (r : ℝ) :
    deriv (fun ρ : ℝ => heatKernel (E := E) t (x + ρ • v - y)) r =
      heatKernel (E := E) t (x + r • v - y) *
        (-(⟪x + r • v - y, v⟫_ℝ / (2 * t))) :=
  (hasDerivAt_heatKernel_spatial_line (E := E) ht x y v r).deriv

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- Fixed-time first-spatial-derivative envelope. -/
def heatKernelFirstSpatialEnvelope (t A : ℝ) (x y : E) : ℝ :=
  heatKernelGaussianPolynomialEnvelope (E := E) t A x y

/-- Constant for the fixed-time first-spatial-derivative domination envelope. -/
def heatKernelFirstSpatialDominationConstant (t C : ℝ) (x v : E) : ℝ :=
  C * ((‖v‖ / (2 * t)) * (3 + 2 * ‖x‖ ^ 2))

/-- Integrability of the fixed-time first-spatial-derivative envelope for `t > 0`. -/
theorem integrable_heatKernelFirstSpatialEnvelope {t : ℝ} (ht : 0 < t) (A : ℝ) (x : E) :
    Integrable (fun y : E => heatKernelFirstSpatialEnvelope (E := E) t A x y) := by
  exact integrable_heatKernelGaussianPolynomialEnvelope (E := E) ht A x

omit [MeasurableSpace E] [BorelSpace E] in
/-- Directional first-spatial Gaussian factor bounded by the envelope polynomial. -/
theorem heatKernel_first_spatial_factor_abs_le {t : ℝ} (ht : 0 < t) (x y v : E) :
    |-(⟪x - y, v⟫_ℝ / (2 * t))| ≤
      ((‖v‖ / (2 * t)) * (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2) := by
  have hden_pos : 0 < 2 * t := by positivity
  have hcoeff_nonneg : 0 ≤ ‖v‖ / (2 * t) := by positivity
  have hinner : |⟪x - y, v⟫_ℝ| ≤ ‖x - y‖ * ‖v‖ :=
    abs_real_inner_le_norm (x - y) v
  have hpoly : ‖x - y‖ ≤ (3 + 2 * ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) :=
    norm_sub_left_le_translate_bound (E := E) x y
  have hmul : ‖x - y‖ * ‖v‖ ≤
      ((3 + 2 * ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) * ‖v‖ :=
    mul_le_mul_of_nonneg_right hpoly (norm_nonneg v)
  calc
    |-(⟪x - y, v⟫_ℝ / (2 * t))| = |⟪x - y, v⟫_ℝ| / (2 * t) := by
      rw [abs_neg, abs_div, abs_of_pos hden_pos]
    _ ≤ (‖x - y‖ * ‖v‖) / (2 * t) :=
      div_le_div_of_nonneg_right hinner hden_pos.le
    _ ≤ (((3 + 2 * ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) * ‖v‖) / (2 * t) :=
      div_le_div_of_nonneg_right hmul hden_pos.le
    _ = ((‖v‖ / (2 * t)) * (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2) := by
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/--
Pointwise domination of the translated first directional spatial derivative
integrand by the fixed-time first-spatial envelope.
-/
theorem heatKernel_first_spatial_line_deriv_sub_left_mul_le_firstSpatialEnvelope
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    (x v y : E) :
    ‖deriv (fun r : ℝ => heatKernel (E := E) t (x + r • v - y)) 0 * f y‖ ≤
      heatKernelFirstSpatialEnvelope (E := E) t
        (heatKernelFirstSpatialDominationConstant (E := E) t C x v) x y := by
  rw [deriv_heatKernel_spatial_line (E := E) ht.ne' x y v 0]
  simp only [zero_smul, add_zero]
  set hk : ℝ := heatKernel (E := E) t (x - y)
  set q : ℝ := -(⟪x - y, v⟫_ℝ / (2 * t))
  set B : ℝ := ((‖v‖ / (2 * t)) * (3 + 2 * ‖x‖ ^ 2)) * (1 + ‖y‖ ^ 2)
  have hk_nonneg : 0 ≤ hk := heatKernel_nonneg (E := E) ht (x - y)
  have hB_nonneg : 0 ≤ B := by positivity
  have hq : |q| ≤ B := by
    simpa [q, B] using heatKernel_first_spatial_factor_abs_le (E := E) ht x y v
  have hnorm_eq : ‖hk * q * f y‖ = hk * |q| * ‖f y‖ := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, Real.norm_eq_abs]
  calc
    ‖hk * q * f y‖ = hk * |q| * ‖f y‖ := hnorm_eq
    _ ≤ hk * B * ‖f y‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq hk_nonneg) (norm_nonneg (f y))
    _ ≤ hk * B * C := by
      exact mul_le_mul_of_nonneg_left (hC y) (mul_nonneg hk_nonneg hB_nonneg)
    _ = heatKernelFirstSpatialEnvelope (E := E) t
        (heatKernelFirstSpatialDominationConstant (E := E) t C x v) x y := by
      simp [heatKernelFirstSpatialEnvelope, heatKernelGaussianPolynomialEnvelope,
        heatKernelFirstSpatialDominationConstant, hk, B]
      ring

end Measurable

end Poincare
