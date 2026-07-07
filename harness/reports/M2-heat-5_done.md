# M2-heat-5 done report: cpow/rpow bridge and heat approximate identity

## Status

New file: `Poincare/Global/HeatApproxIdentity.lean`.

No existing Poincare files were edited, including `Poincare.lean`.

## Completed Lean payload

- `Poincare.heatKernel_fourier_complex_eq_ofReal`: identifies Mathlib's
  Fourier-normalized complex Gaussian at the heat-time scale with
  `(heatKernel t (x - y) : ℂ)` for `0 < t`.
- `Poincare.heatSolution_apply_swap`: records the symmetric `x - y`
  convolution form of `heatSolution`.
- `Poincare.tendsto_heatSolution_nhdsGT_zero`: proves
  `Tendsto (fun t : ℝ => heatSolution t f x) (𝓝[>] 0) (𝓝 (f x))`
  for real-valued integrable `f` continuous at `x`.

## Verification

Required command:

```text
lake build Poincare.Global.HeatApproxIdentity
```

Actual result:

```text
Build completed successfully (2739 jobs).
```
