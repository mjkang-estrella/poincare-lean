# M2-heat-1 assets and done report: model-space heat kernel seed

## Status

New file: `Poincare/Global/HeatKernel.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

Verified command:

```text
lake build Poincare.Global.HeatKernel
```

Actual result: success, `Build completed successfully (2414 jobs)`.

## Pinned Mathlib inventory

Toolchain: `leanprover/lean4:v4.30.0-rc2`.  Mathlib is pinned in
`lake-manifest.json` to `7175569c842f9164564bd76ff8b207e7b4705522`.

| Ingredient | Verdict | Local evidence | Heat-kernel impact |
|---|---:|---|---|
| One-dimensional Gaussian integral | exists | `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` has `integral_gaussian`, `integral_gaussian_complex`, and half-line variants. | Strong base for the one-dimensional normalization proof. |
| Finite-dimensional Gaussian integral | exists | `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` has `GaussianFourier.integral_rexp_neg_mul_sq_norm` and complex variants over finite-dimensional inner-product spaces. | Best route to prove total mass one after a scaling/change-of-variables layer. |
| Fourier transform of Gaussians | exists | `Gaussian/FourierTransform.lean` has `fourierIntegral_gaussian`, `fourier_gaussian_pi`, and `fourier_gaussian_innerProductSpace`. | Useful for semigroup/heat equation proofs in Fourier space. |
| Fourier transform machinery | exists | `Analysis/Fourier/FourierTransform.lean`, `FourierTransformDeriv.lean`, `Inversion.lean`, and `LpSpace.lean`; inversion includes `Real.tendsto_integral_gaussian_smul`. | Enough raw machinery for Schwartz/L2-level model heat evolution, but not a packaged heat semigroup. |
| Convolution | partial | `Analysis/Convolution.lean` defines `MeasureTheory.convolution`, `ConvolutionExistsAt`, `ConvolutionExists`, and `convolution_tendsto_right`; `Analysis/Calculus/ContDiff/Convolution.lean` proves derivative and `ContDiff` results under compact-support hypotheses. | There is usable convolution API and derivative transfer for compactly supported smooth kernels, but no ready Gaussian convolution differentiability theorem. |
| Schwartz space | exists | `Analysis/Distribution/SchwartzSpace/Basic.lean` defines `SchwartzMap` and notation `𝓢(E, F)`; `SchwartzSpace/Deriv.lean` defines derivative/Laplacian operations; `SchwartzSpace/Fourier.lean` gives Fourier continuity and derivative interaction. | Good target space for a first heat semigroup construction. |
| Tempered distributions and Sobolev | partial | `Analysis/Distribution/TemperedDistribution.lean` defines `𝓢'(E, F)`, distributional derivatives, Fourier transform, delta, and Laplacian; `Sobolev.lean` defines `TemperedDistribution.memSobolev` and Sobolev derivative/laplacian facts. | Good Fourier-distribution substrate, but no heat-flow API. |
| Laplacian on inner-product spaces | exists | `Analysis/InnerProductSpace/Laplacian.lean` defines `Δ`, `Δ[s]`, basis formulas, and `laplacian_eq_iteratedDeriv_real`. | The pointwise PDE identity should use this spelling. |
| Heat semigroup / parabolic / Schauder | absent | Searches for `Heat`, `Parabolic`, and PDE-Schauder-specific APIs under `Mathlib/Analysis` and `Mathlib/MeasureTheory` found no heat semigroup/parabolic theory; `Schauder` hits are Schauder bases only. | Front A still needs a new model heat layer and later Schauder/parabolic layers. |

## New Lean payload

`Poincare.Global.HeatKernel` now defines:

```lean
def Poincare.heatKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (t : ℝ) (x : E) : ℝ
```

The formula is
`(4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
  Real.exp (-(‖x‖ ^ 2) / (4 * t))`.

Closed first lemmas:

```lean
theorem Poincare.heatKernel_pos
theorem Poincare.heatKernel_nonneg
theorem Poincare.contDiff_heatKernel_spatial
theorem Poincare.contDiffAt_heatKernel_spatial
```

These are genuine analytic facts: positivity uses `Real.rpow_pos_of_pos`,
`Real.pi_pos`, and `Real.exp_pos`; spatial smoothness uses
`contDiff_norm_sq` and `ContDiff.exp`.

The pointwise heat equation and total-integral-one facts are not claimed in
this slice.  The next obstacle is not missing vocabulary for `Δ`, but the
calculus/algebra bridge for differentiating the full time-dependent Gaussian
normalization and matching it to the Laplacian expression without placeholders.

## Honest verdict

Mathlib has enough Gaussian, Fourier, convolution, Schwartz, tempered
distribution, Sobolev, and Laplacian primitives to begin a model-space heat
kernel development.  It does not have a packaged heat kernel, heat semigroup,
parabolic existence theorem, Schauder estimate, or Gaussian approximate
identity theorem ready to import.

The productive path is therefore model-first:

1. Heat kernel definition and elementary calculus: done here for positivity
   and spatial smoothness on finite-dimensional real inner-product spaces.
2. Smoothing: first prove Gaussian convolution maps bounded/locally integrable
   inputs to smooth functions by adapting existing compact-support convolution
   derivative APIs or by working in Schwartz space via Fourier multipliers.
3. Solves heat equation: prove the pointwise identity first in one dimension
   using `laplacian_eq_iteratedDeriv_real`, then generalize with the
   orthonormal-basis formula in `InnerProductSpace.Laplacian`.
4. Initial data recovery: prove total mass one using
   `GaussianFourier.integral_rexp_neg_mul_sq_norm`, then prove Gaussian
   approximate identity convergence; existing `convolution_tendsto_right` is
   a template but is currently compact-support/nonnegative-kernel oriented.
5. Uniqueness: start with Schwartz or compactly supported smooth solutions and
   Fourier/energy methods, then generalize to Sobolev/tempered-distribution
   uniqueness before attempting closed-manifold parabolic uniqueness.
