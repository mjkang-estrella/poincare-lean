# M2-heat-7 blocked report: heat-kernel Cauchy close

## Status

New file: `Poincare/Global/HeatCauchyClose.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

The full task remains blocked.  I did not add the two requested interchange
lemmas or the unconditional Cauchy theorem, because doing so would require
postulating the analytic domination estimates that the worker contract forbids
faking.

## Verified Lean payload

- `Poincare.heatKernelTimeDerivAbsMajorant`: the explicit absolute-value
  majorant obtained from the product-rule formula in `deriv_heatKernel_time`.
- `Poincare.heatKernel_time_deriv_mul_le_abs_majorant`: for bounded data,
  `‖deriv (fun σ => heatKernel σ u) τ * f y‖` is bounded by that explicit
  majorant at every positive time `τ`.
- `Poincare.heatKernel_time_deriv_sub_left_mul_le_abs_majorant`: the same
  estimate in the shifted convolution form `x - y`.
- `Poincare.heatKernel_time_window_pos`: every `τ ∈ [t / 2, 2 * t]` is positive
  when `0 < t`.
- `Poincare.heatKernel_time_deriv_window_sub_left_mul_le_abs_majorant`: the
  shifted pointwise estimate on the standard compact time window.

## Isolated domination estimate

The verified pointwise estimate is:

```lean
theorem heatKernel_time_deriv_window_sub_left_mul_le_abs_majorant {t τ C : ℝ}
    (ht : 0 < t) (hτ : τ ∈ Set.Icc (t / 2) (2 * t))
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤
      heatKernelTimeDerivAbsMajorant (E := E) τ C (x - y)
```

This uses the explicit `deriv_heatKernel_time` formula and the bounded-data
hypothesis.  The remaining time-interchange gap is to replace the right-hand
side, uniformly for `τ ∈ [t / 2, 2 * t]`, by a single integrable translated
Gaussian-polynomial envelope and feed it to
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

The spatial Laplacian interchange is still further away: Mathlib's available
convolution derivative lemmas in `Analysis/Calculus/ContDiff/Convolution.lean`
require compact support of the differentiable convolution factor, while the
heat kernel has Gaussian tails.  A second-derivative parametric-integral proof
therefore needs the analogous fixed integrable envelope for the second spatial
derivatives of the translated heat kernel.

## Verification

Required command:

```text
lake build Poincare.Global.HeatCauchyClose
```

Actual result:

```text
Build completed successfully (2743 jobs).
```
