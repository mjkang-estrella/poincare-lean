import Poincare.Global.HeatCauchyClose
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Heat-kernel Gaussian-polynomial envelopes

This module isolates the Gaussian moment estimate needed for the heat-kernel
Cauchy problem envelope work.  The estimates below are nonconditional
integrability facts for the classical translated Gaussian-polynomial shapes.

The domination of the time derivative and the spatial second derivatives by
these envelopes is not asserted here; that is the remaining analytic boundary.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Arbitrary-scale finite-dimensional Gaussian integrability. -/
theorem integrable_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-a * ‖x‖ ^ 2)) := by
  have hcomplex :
      Integrable
        (fun x : E => Complex.exp (-(a : ℂ) * (‖x‖ ^ 2 : ℂ))) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (a : ℂ)) (c := 0) (w := (0 : E)) (by simpa using ha)
  convert hcomplex.re using 2 with x
  rw [← Complex.exp_ofReal_re (-a * ‖x‖ ^ 2)]
  congr 1
  push_cast
  ring

/--
The basic second Gaussian moment estimate.

The proof widens the Gaussian by bounding the quadratic factor with an
exponential: with `q = (a / 2) * ‖x‖²`, `q ≤ exp q`, so the moment is dominated
by a sum of two integrable Gaussians.
-/
theorem integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E => (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hga : Integrable (fun x : E => Real.exp (-a * ‖x‖ ^ 2)) :=
    integrable_exp_neg_mul_norm_sq (E := E) ha
  have hhalf_pos : 0 < a / 2 := half_pos ha
  have hghalf : Integrable (fun x : E => Real.exp (-(a / 2) * ‖x‖ ^ 2)) :=
    integrable_exp_neg_mul_norm_sq (E := E) hhalf_pos
  have hbound : ∀ x : E,
      ‖(1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2)‖ ≤
        Real.exp (-a * ‖x‖ ^ 2) + (2 / a) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
    intro x
    set r2 : ℝ := ‖x‖ ^ 2
    have hr2_nonneg : 0 ≤ r2 := by simp [r2]
    have hq_le_exp : (a / 2) * r2 ≤ Real.exp ((a / 2) * r2) := by
      exact (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp ((a / 2) * r2))
    have hscale_nonneg : 0 ≤ 2 / a := div_nonneg (by norm_num) ha.le
    have hr2_le : r2 ≤ (2 / a) * Real.exp ((a / 2) * r2) := by
      calc
        r2 = (2 / a) * ((a / 2) * r2) := by field_simp [ha.ne']
        _ ≤ (2 / a) * Real.exp ((a / 2) * r2) :=
          mul_le_mul_of_nonneg_left hq_le_exp hscale_nonneg
    have h_exp_nonneg : 0 ≤ Real.exp (-a * r2) := (Real.exp_pos _).le
    have hpoly_nonneg : 0 ≤ 1 + r2 := by linarith
    have hprod :
        Real.exp ((a / 2) * r2) * Real.exp (-a * r2) =
          Real.exp (-(a / 2) * r2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ‖(1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2)‖ =
          (1 + r2) * Real.exp (-a * r2) := by
            simpa [r2] using Real.norm_of_nonneg
              (mul_nonneg hpoly_nonneg h_exp_nonneg)
      _ = Real.exp (-a * r2) + r2 * Real.exp (-a * r2) := by ring
      _ ≤ Real.exp (-a * r2) +
          ((2 / a) * Real.exp ((a / 2) * r2)) * Real.exp (-a * r2) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hr2_le h_exp_nonneg)
      _ = Real.exp (-a * r2) +
          (2 / a) * (Real.exp ((a / 2) * r2) * Real.exp (-a * r2)) := by ring
      _ = Real.exp (-a * r2) + (2 / a) * Real.exp (-(a / 2) * r2) := by
            rw [hprod]
      _ = Real.exp (-a * ‖x‖ ^ 2) +
          (2 / a) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by simp [r2]
  have hmeas :
      AEStronglyMeasurable
        (fun x : E => (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2)) volume := by
    have hnormsq : Continuous fun x : E => ‖x‖ ^ 2 := continuous_norm.pow 2
    have harg : Continuous fun x : E => (-a) * ‖x‖ ^ 2 := continuous_const.mul hnormsq
    have hexp : Continuous fun x : E => Real.exp (-a * ‖x‖ ^ 2) := by
      simpa [neg_mul] using harg.rexp
    exact ((continuous_const.add hnormsq).mul hexp).aestronglyMeasurable
  refine Integrable.mono' (hga.add (hghalf.const_mul (2 / a))) hmeas ?_
  exact Filter.Eventually.of_forall hbound

/-- The centered Gaussian-polynomial moment remains integrable after `y ↦ x - y`. -/
theorem integrable_one_add_norm_sq_sub_left_mul_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a)
    (x : E) :
    Integrable (fun y : E => (1 + ‖x - y‖ ^ 2) * Real.exp (-a * ‖x - y‖ ^ 2)) := by
  exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) ha).comp_sub_left x

/-- Centered Gaussian-polynomial integrability in heat-kernel normalization. -/
theorem integrable_one_add_norm_sq_sub_left_mul_heatKernel {s : ℝ} (hs : 0 < s)
    (x : E) :
    Integrable (fun y : E => (1 + ‖x - y‖ ^ 2) * heatKernel (E := E) s (x - y)) := by
  have ha : 0 < 1 / (4 * s) := by positivity
  have h :=
    (integrable_one_add_norm_sq_sub_left_mul_exp_neg_mul_norm_sq (E := E) ha x).const_mul
      ((4 * Real.pi * s) ^ (-(Module.finrank ℝ E : ℝ) / 2))
  have hfun :
      (fun y : E => (1 + ‖x - y‖ ^ 2) * heatKernel (E := E) s (x - y)) =
        fun y : E => (4 * Real.pi * s) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          ((1 + ‖x - y‖ ^ 2) * Real.exp (-(1 / (4 * s)) * ‖x - y‖ ^ 2)) := by
    funext y
    unfold heatKernel
    have hexp : -‖x - y‖ ^ 2 / (4 * s) = -(1 / (4 * s)) * ‖x - y‖ ^ 2 := by
      field_simp [hs.ne']
    rw [hexp]
    ring
  rw [hfun]
  exact h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A translated quadratic polynomial is bounded by a centered quadratic polynomial. -/
theorem one_add_norm_sq_le_translate_bound (x y : E) :
    1 + ‖y‖ ^ 2 ≤ (3 + 2 * ‖x‖ ^ 2) * (1 + ‖x - y‖ ^ 2) := by
  have hy_norm : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc
      ‖y‖ = ‖x - (x - y)‖ := by
        congr 1
        abel
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le x (x - y)
  have hy_sq_le : ‖y‖ ^ 2 ≤ (‖x‖ + ‖x - y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg y) hy_norm 2
  have hquad : (‖x‖ + ‖x - y‖) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖x - y‖)]
  have hy_sq_bound : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 :=
    hy_sq_le.trans hquad
  have hx_nonneg : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  have hu_nonneg : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
  nlinarith

/--
The classical translated heat-kernel envelope with polynomial `(1 + ‖y‖²)` is integrable.
-/
theorem integrable_one_add_norm_sq_mul_heatKernel_sub_left {s : ℝ} (hs : 0 < s)
    (x : E) :
    Integrable (fun y : E => (1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y)) := by
  have hcenter :=
    (integrable_one_add_norm_sq_sub_left_mul_heatKernel (E := E) hs x).const_mul
      (3 + 2 * ‖x‖ ^ 2)
  have hmeas :
      AEStronglyMeasurable
        (fun y : E => (1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y)) volume := by
    have hynormsq : Continuous fun y : E => ‖y‖ ^ 2 := continuous_norm.pow 2
    have hsub : Continuous fun y : E => x - y := continuous_const.sub continuous_id
    have hk : Continuous fun y : E => heatKernel (E := E) s (x - y) :=
      (contDiff_heatKernel_spatial (E := E) s).continuous.comp hsub
    exact ((continuous_const.add hynormsq).mul hk).aestronglyMeasurable
  refine Integrable.mono' hcenter hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hk_nonneg : 0 ≤ heatKernel (E := E) s (x - y) :=
    heatKernel_nonneg (E := E) hs (x - y)
  have hleft_nonneg : 0 ≤ (1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y) := by
    positivity
  calc
    ‖(1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y)‖ =
        (1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y) :=
          Real.norm_of_nonneg hleft_nonneg
    _ ≤ ((3 + 2 * ‖x‖ ^ 2) * (1 + ‖x - y‖ ^ 2)) *
        heatKernel (E := E) s (x - y) :=
          mul_le_mul_of_nonneg_right (one_add_norm_sq_le_translate_bound x y) hk_nonneg
    _ = (3 + 2 * ‖x‖ ^ 2) *
        ((1 + ‖x - y‖ ^ 2) * heatKernel (E := E) s (x - y)) := by ring

/-- The common Gaussian-polynomial envelope shape used by the heat-kernel estimates. -/
def heatKernelGaussianPolynomialEnvelope (s A : ℝ) (x y : E) : ℝ :=
  A * ((1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y))

/-- Integrability of the common Gaussian-polynomial envelope shape. -/
theorem integrable_heatKernelGaussianPolynomialEnvelope {s : ℝ} (hs : 0 < s)
    (A : ℝ) (x : E) :
    Integrable (fun y : E => heatKernelGaussianPolynomialEnvelope (E := E) s A x y) := by
  exact (integrable_one_add_norm_sq_mul_heatKernel_sub_left (E := E) hs x).const_mul A

/-- Positive-time window candidate for the time-derivative domination envelope. -/
def heatKernelTimeWindowEnvelope (t A : ℝ) (x y : E) : ℝ :=
  heatKernelGaussianPolynomialEnvelope (E := E) (2 * t) A x y

/-- Integrability of the time-window candidate envelope for `t > 0`. -/
theorem integrable_heatKernelTimeWindowEnvelope {t : ℝ} (ht : 0 < t) (A : ℝ) (x : E) :
    Integrable (fun y : E => heatKernelTimeWindowEnvelope (E := E) t A x y) := by
  exact integrable_heatKernelGaussianPolynomialEnvelope (E := E) (by positivity) A x

/-- Fixed-time candidate envelope for the spatial second-derivative/Laplacian interchange. -/
def heatKernelLaplacianEnvelope (t A : ℝ) (x y : E) : ℝ :=
  heatKernelGaussianPolynomialEnvelope (E := E) t A x y

/-- Integrability of the fixed-time Laplacian candidate envelope for `t > 0`. -/
theorem integrable_heatKernelLaplacianEnvelope {t : ℝ} (ht : 0 < t) (A : ℝ) (x : E) :
    Integrable (fun y : E => heatKernelLaplacianEnvelope (E := E) t A x y) := by
  exact integrable_heatKernelGaussianPolynomialEnvelope (E := E) ht A x

end Poincare
