# M2-heat-4 blocked report: heat-kernel mass and convolution layer

## Status

New file: `Poincare/Global/HeatKernelIntegral.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

Verified command:

```text
lake build Poincare.Global.HeatKernelIntegral
```

Actual result:

```text
Build completed successfully (2738 jobs).
```

## Completed Lean payload

The new module proves, for a finite-dimensional real inner-product space with
its Borel measurable structure and canonical volume measure:

- `Poincare.heatKernel_integrable`: for `0 < t`, `x ↦ heatKernel t x` is integrable.
- `Poincare.integral_heatKernel_eq_one`: for `0 < t`, `∫ x, heatKernel t x = 1`.
- `Poincare.heatSolution`: the convolution definition
  `MeasureTheory.convolution (heatKernel t) f (ContinuousLinearMap.lsmul ℝ ℝ) volume`.
- `Poincare.heatSolution_apply`: the defining integral formula.
- `Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous`: pointwise integrability of
  the convolution integrand for bounded continuous real-valued data.
- `Poincare.heatKernel_convolutionExists_of_bounded_continuous`: everywhere convolution
  existence for bounded continuous real-valued data.
- `Poincare.continuous_heatSolution_of_bounded_continuous`: continuity of the heat solution
  under the same bounded continuous hypotheses.
- `Poincare.gaussianApproxIdentity_heatTimeScale_complex`: Mathlib's Fourier-normalized
  complex Gaussian approximate identity, composed with the heat-time scale
  `c = (4π²t)⁻¹`.

## Blocked item

The exact real statement

```lean
Tendsto (fun t : ℝ => heatSolution t f x) (𝓝[>] 0) (𝓝 (f x))
```

is not proved yet.

Mathlib reaches the convergence theorem in the complex Fourier-normalized form

```lean
((π : ℂ) * (4π²t)⁻¹) ^ (finrank / 2)
  * Complex.exp (-(π : ℂ)^2 * (4π²t)⁻¹ * ‖x - y‖^2)
```

for integrable data continuous at `x`.  The remaining bridge is a nontrivial
coercion/normalization lemma identifying that expression with the real
`heatKernel t (x - y)` normalization using `Complex.cpow` versus `Real.rpow`.

I left this as a precise boundary rather than adding an unverified or fragile
wrapper theorem.
