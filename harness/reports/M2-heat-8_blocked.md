# M2-heat-8 blocked report: heat-kernel integrable envelopes

## Status

New file: `Poincare/Global/HeatEnvelopes.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

This is a verified partial.  The full task remains blocked: I did not prove the
uniform pointwise domination of the time derivative or the second spatial
derivatives by the candidate envelopes, so I did not discharge the two
conditional interchange hypotheses from `HeatCauchy.lean` and did not state an
unconditional Cauchy theorem.

## Verified Lean payload

- `Poincare.integrable_exp_neg_mul_norm_sq`: arbitrary positive-scale Gaussian
  integrability on finite-dimensional real inner-product spaces.
- `Poincare.integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq`: the second
  Gaussian moment estimate.  The proof widens the Gaussian using
  `q ≤ exp q`, reducing the polynomial moment to a sum of two integrable
  Gaussians.
- `Poincare.integrable_one_add_norm_sq_sub_left_mul_exp_neg_mul_norm_sq`: the
  centered translated version under `y ↦ x - y`.
- `Poincare.integrable_one_add_norm_sq_sub_left_mul_heatKernel`: centered
  heat-kernel normalized Gaussian-polynomial integrability.
- `Poincare.one_add_norm_sq_le_translate_bound`: the polynomial translation
  inequality
  `1 + ‖y‖² ≤ (3 + 2 * ‖x‖²) * (1 + ‖x - y‖²)`.
- `Poincare.integrable_one_add_norm_sq_mul_heatKernel_sub_left`: the classical
  envelope shape requested in the task,
  `(1 + ‖y‖²) * heatKernel s (x - y)`, is integrable for every `0 < s`.
- Candidate envelope definitions and integrability proofs:
  `heatKernelGaussianPolynomialEnvelope`,
  `integrable_heatKernelGaussianPolynomialEnvelope`,
  `heatKernelTimeWindowEnvelope`,
  `integrable_heatKernelTimeWindowEnvelope`,
  `heatKernelLaplacianEnvelope`,
  `integrable_heatKernelLaplacianEnvelope`.

## Isolated remaining estimate

The proved integrability target is:

```lean
theorem integrable_one_add_norm_sq_mul_heatKernel_sub_left {s : ℝ} (hs : 0 < s)
    (x : E) :
    Integrable (fun y : E => (1 + ‖y‖ ^ 2) * heatKernel (E := E) s (x - y))
```

The remaining time-derivative step is the pointwise domination, for some
constant `A = A(t, C, x)` independent of `τ` and `y`,

```lean
∀ τ ∈ Set.Icc (t / 2) (2 * t), ∀ y,
  ‖deriv (fun σ : ℝ => heatKernel (E := E) σ (x - y)) τ * f y‖ ≤
    heatKernelTimeWindowEnvelope (E := E) t A x y
```

under the bounded-data hypothesis `∀ y, ‖f y‖ ≤ C`.

The analogous spatial blocker is the corresponding pointwise estimate for the
second spatial derivatives/orthonormal-basis Laplacian terms of
`z ↦ heatKernel t (z - y)`, followed by the parametric-integral argument that
moves those second derivatives through the convolution integral.

## Verification

Required command:

```text
lake build Poincare.Global.HeatEnvelopes
```

Actual result:

```text
Build completed successfully (2744 jobs).
```
