import Poincare.Global.HeatCauchyTheorem

/-!
# Frechet heat-kernel Cauchy work surface

This file is the `M2-heat-12` work surface.  The full twice-Frechet dominated
differentiation route needs spatially local operator-valued domination.  The
verified payload below isolates the first such operator estimate: the Frechet
derivative integrand for `x ↦ heatKernel t (x - y) * c` is dominated, in
operator norm, by the Gaussian-polynomial envelope already used by the scalar
directional estimates.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
The spatial Frechet derivative integrand for the translated heat kernel,
with the data value left as a scalar parameter.
-/
def heatKernelSpatialFDerivIntegrand (t : ℝ) (x y : E) (c : ℝ) : E →L[ℝ] ℝ :=
  (c * heatKernel (E := E) t (x - y) * (-(1 / (2 * t)))) • innerSL ℝ (x - y)

/-- Operator-norm domination constant for the first spatial Frechet integrand. -/
def heatKernelSpatialFDerivOpDominationConstant (t C : ℝ) (x : E) : ℝ :=
  C * ((1 / (2 * t)) * (3 + 2 * ‖x‖ ^ 2))

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/--
First Frechet-operator domination estimate for the translated heat-kernel
integrand.

This is the operator-valued analogue of the scalar first-directional envelope:
after applying the Frechet derivative to an arbitrary direction and taking the
operator norm, the same Gaussian-polynomial family controls the result.
-/
theorem heatKernel_spatial_fderiv_integrand_norm_le_firstSpatialEnvelope
    {t C c : ℝ} (ht : 0 < t) (hc : ‖c‖ ≤ C) (x y : E) :
    ‖heatKernelSpatialFDerivIntegrand (E := E) t x y c‖ ≤
      heatKernelFirstSpatialEnvelope (E := E) t
        (heatKernelSpatialFDerivOpDominationConstant (E := E) t C x) x y := by
  set hk : ℝ := heatKernel (E := E) t (x - y)
  set K : ℝ := 3 + 2 * ‖x‖ ^ 2
  set P : ℝ := 1 + ‖y‖ ^ 2
  have hC_nonneg : 0 ≤ C := (norm_nonneg c).trans hc
  have hk_nonneg : 0 ≤ hk := heatKernel_nonneg (E := E) ht (x - y)
  have hcoeff_nonneg : 0 ≤ C * hk * (1 / (2 * t)) := by positivity
  have hM_nonneg :
      0 ≤ heatKernelFirstSpatialEnvelope (E := E) t
        (heatKernelSpatialFDerivOpDominationConstant (E := E) t C x) x y := by
    simp [heatKernelFirstSpatialEnvelope, heatKernelGaussianPolynomialEnvelope,
      heatKernelSpatialFDerivOpDominationConstant]
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM_nonneg ?_
  intro v
  have hcoeff :
      ‖c * hk * (-(1 / (2 * t)))‖ ≤ C * hk * (1 / (2 * t)) := by
    have hinv_nonneg : 0 ≤ 1 / (2 * t) := by positivity
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
      Real.norm_of_nonneg hinv_nonneg]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hk_nonneg) hinv_nonneg
  have hinner : ‖innerSL ℝ (x - y) v‖ ≤ ‖x - y‖ * ‖v‖ := by
    simpa only [innerSL_apply_apply, Real.norm_eq_abs] using abs_real_inner_le_norm (x - y) v
  have hpoly : ‖x - y‖ ≤ K * P := by
    simpa [K, P] using norm_sub_left_le_translate_bound (E := E) x y
  calc
    ‖heatKernelSpatialFDerivIntegrand (E := E) t x y c v‖ =
        ‖c * hk * (-(1 / (2 * t)))‖ * ‖innerSL ℝ (x - y) v‖ := by
          simp [heatKernelSpatialFDerivIntegrand, hk]
    _ ≤ (C * hk * (1 / (2 * t))) * (‖x - y‖ * ‖v‖) := by
      exact mul_le_mul hcoeff hinner (norm_nonneg _) hcoeff_nonneg
    _ ≤ (C * hk * (1 / (2 * t))) * ((K * P) * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (norm_nonneg v)) hcoeff_nonneg
    _ =
        heatKernelFirstSpatialEnvelope (E := E) t
          (heatKernelSpatialFDerivOpDominationConstant (E := E) t C x) x y * ‖v‖ := by
      simp [heatKernelFirstSpatialEnvelope, heatKernelGaussianPolynomialEnvelope,
        heatKernelSpatialFDerivOpDominationConstant, hk, K, P]
      ring

end Measurable

end Poincare
