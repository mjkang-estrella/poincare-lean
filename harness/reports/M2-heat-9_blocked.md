# M2-heat-9 blocked report: pointwise-to-envelope final feeds

## Status

New file: `Poincare/Global/HeatCauchyFinal.lean`.

No existing Poincare source file was edited, including `Poincare.lean`.

This is verified progress, but not the unconditional Cauchy theorem.  The time
side is closed: the pointwise time-window domination is proved and fed through
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.  The spatial side has the
requested fixed-envelope pointwise Laplacian domination, but the actual
Laplacian-under-the-integral theorem remains blocked on a second-derivative
parametric-integral argument.  The available Mathlib theorem naturally asks for
Fréchet/CLM-valued derivative bounds; the scalar Laplacian envelope below is
not by itself enough to identify `Δ (fun z => ∫ y, ...) x` with the integral of
the scalar Laplacian.

## Verified Lean payload

- `Poincare.deriv_heatKernel_time_eq_heatKernel_mul`: factored time derivative.
- `Poincare.laplacian_heatKernel_sub_left_eq_heatKernel_mul`: factored
  translated spatial Laplacian.
- `Poincare.heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope`:
  pointwise domination by `heatKernelTimeWindowEnvelope`.
- `Poincare.laplacian_heatKernel_sub_left_mul_le_laplacianEnvelope`: pointwise
  spatial Laplacian domination by `heatKernelLaplacianEnvelope`.
- `Poincare.heatKernel_time_deriv_integral_hasDerivAt`: time differentiation
  under the convolution integral.
- `Poincare.heatSolution_solves_heatEquation_of_spatial_interchange` and
  `Poincare.heatSolution_model_cauchy_problem_of_spatial_interchange`: the
  `HeatCauchy.lean` conditional package with the time hypothesis discharged,
  leaving only the spatial interchange hypothesis.

## Remaining estimate

The remaining theorem-level blocker is to turn the verified scalar pointwise
domination into the actual spatial Laplacian interchange:

```lean
theorem laplacian_heatKernel_sub_left_mul_le_laplacianEnvelope {t C : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x y : E) :
    ‖(Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y‖ ≤
      heatKernelLaplacianEnvelope (E := E) t
        (heatKernelLaplacianDominationConstant (E := E) t C x) x y
```

This is the integrable envelope needed for the scalar Laplacian integrand.  The
missing bridge is a Lean proof that the Laplacian of the parameter integral is
the integral of these Laplacian terms.

## Verification

Required command:

```text
lake build Poincare.Global.HeatCauchyFinal
```

Actual result:

```text
Build completed successfully (2746 jobs).
```
