# M2-heat-6 blocked report: heatSolution heat-equation Cauchy interface

## Status

New file: `Poincare/Global/HeatCauchy.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

This is a strict partial.  The full bounded-continuous-data Cauchy theorem is
still blocked on the analytic differentiation/interchange estimates for the
convolution integral.

## Verified Lean payload

- `Poincare.heatKernel_integrable_sub_left`: positive-time heat kernels remain
  integrable after the translation `y ↦ x - y`.
- `Poincare.heatKernel_bounded_data_domination`: bounded measurable data in the
  symmetric convolution form satisfy the pointwise domination
  `‖heatKernel t (x - y) * f y‖ ≤ C * heatKernel t (x - y)`, with the dominating
  translated kernel integrable, and hence the bounded-data integrand integrable.
- `Poincare.laplacian_heatKernel_sub_left`: spatial Laplacian commutes with
  translation of the heat kernel.
- `Poincare.heatKernel_sub_left_heatEquation_laplacian`: the already-certified
  kernel heat equation in translated `x - y` form.
- Conditional interface theorems:
  `deriv_heatSolution_eq_integral_of_hasDerivAt_integral`,
  `laplacian_heatSolution_eq_integral_deriv_of_spatial_interchange`,
  `heatSolution_solves_heatEquation_of_differentiation_under_integral`, and
  `heatSolution_model_cauchy_problem_of_differentiation_under_integral`.

## Blocked item

The requested unconditional theorem

```lean
deriv (fun τ : ℝ => heatSolution τ f x) t =
  (Δ fun z => heatSolution t f z) x
```

for `0 < t` and bounded integrable/continuous `f` is not proved yet.

The missing work is the genuine Gaussian domination needed to apply Mathlib's
parametric-integral theorem to

```lean
fun τ : ℝ => ∫ y, heatKernel τ (x - y) * f y
```

and the corresponding spatial second-derivative/Laplacian interchange through
the convolution integral.  The existing kernel PDE and approximate-identity
recovery are enough once those two interchange facts are supplied, as shown by
the conditional packaged theorem in `HeatCauchy.lean`.

## Verification

Required command:

```text
lake build Poincare.Global.HeatCauchy
```

Actual result:

```text
Build completed successfully (2742 jobs).
```
