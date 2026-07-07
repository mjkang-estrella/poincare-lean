# M2-heat-3 done report: n-dimensional heat equation

## Status

New Lean file:

- `Poincare/Global/HeatKernelPDEn.lean`

No existing Lean files were edited, including `Poincare.lean`.

Verified command:

```text
lake build Poincare.Global.HeatKernelPDEn
```

Actual result:

```text
✔ [2487/2487] Built Poincare.Global.HeatKernelPDEn (2.9s)
Build completed successfully (2487 jobs).
```

## Closed payload

The new module imports `Poincare.Global.HeatKernelPDE` and proves reusable
spatial Gaussian calculus lemmas:

```lean
theorem Poincare.hasFDerivAt_neg_norm_sq_div
theorem Poincare.hasFDerivAt_exp_neg_norm_sq_div
theorem Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply
theorem Poincare.sum_sq_inner_stdOrthonormalBasis
theorem Poincare.laplacian_exp_neg_norm_sq_div
```

The final theorem is the requested finite-dimensional inner-product-space heat
equation in Mathlib's Laplacian notation:

```lean
theorem Poincare.heatKernel_heatEquation_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    deriv (fun τ : ℝ ↦ heatKernel (E := E) τ x) t =
      (Δ fun y : E ↦ heatKernel (E := E) t y) x
```

Spelling adaptation from the isolated target: the proof uses explicit
`(E := E)` arguments to match the existing `heatKernel` API; the mathematical
statement and Laplacian target are unchanged.
