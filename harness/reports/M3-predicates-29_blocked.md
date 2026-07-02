# M3-predicates-29 progress report

## Summed flat-torus sanity check

The two previous pointwise intermediates fail on the flat two-torus with
standard parallel frame and metric variation

```text
h_11 = cos y,   all other h_ij = 0.
```

At `y = 0`, the divergence-order pointwise trace for `u = w = e_1` is

```text
Σ_i ∂_i δΓ^i_11 = 1/2,
```

while the false pointwise inner-trace derivative is `0`.  The fully summed
target instead takes the raised trace over the lower slots:

```text
Σ_j Σ_i ∂_i δΓ^i_jj.
```

The only nonzero contribution is still the `j = 1, i = 2` term:

```text
Σ_j Σ_i ∂_i δΓ^i_jj = ∂_2 δΓ^2_11 = 1/2.
```

The right side of the intended keystone is

```text
div div h - 1/2 Δ(tr h).
```

For this variation,

```text
div div h = ∂_1∂_1 h_11 = 0,
tr h = cos y,
Δ(tr h) = ∂_2∂_2 cos y = -1 at y = 0,
```

so

```text
div div h - 1/2 Δ(tr h) = 0 - 1/2(-1) = 1/2.
```

Thus the double trace repairs the false pointwise identity and matches the
model keystone shape.

## Current proof status

In progress.  The direct route should bypass
`DeltaGammaInnerTraceFieldCovariantDerivativeAt` and target the summed
`DeltaGammaDivergenceTraceHessianAssemblyAt` from `covDeltaGamma_koszul`.
