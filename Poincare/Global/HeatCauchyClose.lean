import Poincare.Global.HeatCauchy

/-!
# Heat-kernel Cauchy close attempt

This file is intentionally a verified partial for `M2-heat-7`.

The conditional Cauchy package in `Poincare.Global.HeatCauchy` reduces the
model Cauchy theorem to two genuine analytic interchange statements.  The
first step below isolates the honest pointwise domination seed for the time
derivative of the heat-kernel integrand.  It uses the explicit
`deriv_heatKernel_time` formula and the bounded-data hypothesis; no
interchange lemma is postulated.

The remaining blocked step is upgrading this pointwise majorant on a compact
positive time window to one fixed integrable Gaussian-polynomial envelope, and
then proving the corresponding second-spatial-derivative envelope for the
Laplacian interchange.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/--
The absolute-value majorant obtained directly from the explicit product-rule
formula for the positive-time heat-kernel derivative.

This is not yet the fixed integrable envelope needed by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`: the remaining analytic
work is to dominate this uniformly for `τ` in a compact window around a fixed
positive time by a single integrable Gaussian times a polynomial.
-/
def heatKernelTimeDerivAbsMajorant (τ C : ℝ) (u : E) : ℝ :=
  (‖((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
          (4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) *
          Real.exp (-(‖u‖ ^ 2) / (4 * τ))‖ +
      ‖(4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          (Real.exp (-(‖u‖ ^ 2) / (4 * τ)) * (‖u‖ ^ 2 / (4 * τ ^ 2)))‖) * C

/--
Pointwise bounded-data domination for the time derivative of the heat-kernel
integrand.

This is the non-vacuous estimate that the compact-window proof must sharpen:
after bounding the two `τ`-dependent coefficients and the exponential uniformly
on `[t / 2, 2 * t]`, the right-hand side should be replaced by one fixed
integrable Gaussian-polynomial bound.
-/
theorem heatKernel_time_deriv_mul_le_abs_majorant {τ C : ℝ} (hτ : 0 < τ)
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (u y : E) :
    ‖deriv (fun σ : ℝ => heatKernel (E := E) σ u) τ * f y‖ ≤
      heatKernelTimeDerivAbsMajorant (E := E) τ C u := by
  rw [deriv_heatKernel_time (E := E) hτ u]
  set a : ℝ :=
    ((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
        (4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) *
        Real.exp (-(‖u‖ ^ 2) / (4 * τ))
  set b : ℝ :=
    (4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        (Real.exp (-(‖u‖ ^ 2) / (4 * τ)) * (‖u‖ ^ 2 / (4 * τ ^ 2)))
  have hmul :
      ‖(a + b) * f y‖ ≤ (‖a‖ + ‖b‖) * C := by
    calc
      ‖(a + b) * f y‖ = ‖a + b‖ * ‖f y‖ := norm_mul _ _
      _ ≤ (‖a‖ + ‖b‖) * C :=
          mul_le_mul (norm_add_le a b) (hC y) (norm_nonneg _) (by positivity)
  simpa [heatKernelTimeDerivAbsMajorant, a, b] using hmul

/-- Shifted `x - y` form of `heatKernel_time_deriv_mul_le_abs_majorant`. -/
theorem heatKernel_time_deriv_sub_left_mul_le_abs_majorant {τ C : ℝ} (hτ : 0 < τ)
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤
      heatKernelTimeDerivAbsMajorant (E := E) τ C (x - y) :=
  heatKernel_time_deriv_mul_le_abs_majorant (E := E) hτ hC (x - y) y

/-- Positivity of every time in the standard compact window around `t > 0`. -/
theorem heatKernel_time_window_pos {t τ : ℝ} (ht : 0 < t)
    (hτ : τ ∈ Set.Icc (t / 2) (2 * t)) :
    0 < τ := by
  exact (half_pos ht).trans_le hτ.1

/--
Window-local pointwise domination for the shifted heat-kernel time derivative.

The majorant still depends on `τ`; this theorem isolates the exact remaining
gap for the requested time-interchange lemma: remove the `τ` dependence on
`Set.Icc (t / 2) (2 * t)` and prove integrability of the resulting translated
Gaussian-polynomial bound.
-/
theorem heatKernel_time_deriv_window_sub_left_mul_le_abs_majorant {t τ C : ℝ}
    (ht : 0 < t) (hτ : τ ∈ Set.Icc (t / 2) (2 * t))
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤
      heatKernelTimeDerivAbsMajorant (E := E) τ C (x - y) :=
  heatKernel_time_deriv_sub_left_mul_le_abs_majorant (E := E)
    (heatKernel_time_window_pos ht hτ) hC x y

end Poincare
