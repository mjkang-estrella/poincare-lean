# M2-heat-2 done report: heat-kernel PDE slice

## Status

New Lean file:

- `Poincare/Global/HeatKernelPDE.lean`

No existing Lean files were edited, including `Poincare.lean`.

Verified command:

```text
lake build Poincare.Global.HeatKernelPDE
```

Actual result:

```text
Build completed successfully (2486 jobs).
```

## Closed payload

The new module imports `Poincare.Global.HeatKernel` and proves:

```lean
theorem Poincare.hasDerivAt_heatKernel_time
theorem Poincare.deriv_heatKernel_time
```

These give positive-time differentiability of `t ↦ heatKernel t x` for any
finite-dimensional real inner-product space, with the derivative written in
explicit product-rule form.

For the one-dimensional Gaussian, the file defines the unfolded real formula

```lean
def Poincare.heatKernelReal (t x : ℝ) : ℝ
```

and proves the bridge

```lean
theorem Poincare.heatKernel_real_eq
```

from `heatKernel (E := ℝ)` to the unfolded formula.  It then proves the
pointwise one-dimensional heat equation in both second-derivative and
Laplacian notation:

```lean
theorem Poincare.heatKernelReal_heatEquation
theorem Poincare.heatKernel_real_heatEquation
theorem Poincare.heatKernel_real_heatEquation_laplacian
```

The final theorem is:

```lean
theorem Poincare.heatKernel_real_heatEquation_laplacian {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ ↦ heatKernel (E := ℝ) τ x) t =
      (Δ fun y : ℝ ↦ heatKernel (E := ℝ) t y) x
```

## Higher-dimensional boundary

The n-dimensional identity was not closed in this slice.  The exact intended
statement, using Mathlib's Laplacian contraction over the canonical covariant
tensor, is:

```lean
theorem heatKernel_heatEquation_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    deriv (fun τ : ℝ ↦ heatKernel (E := E) τ x) t =
      (Δ fun y : E ↦ heatKernel (E := E) t y) x
```

The needed next step is the spatial second-Fréchet derivative computation for
`x ↦ Real.exp (-(‖x‖ ^ 2) / (4 * t))`, then contraction with
`InnerProductSpace.canonicalCovariantTensor E` or equivalently the
orthonormal-basis formula from `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`.
