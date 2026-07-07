# M5-rigid-8 blocked: Cartan local isometry strict partial

## Artifact

- Added `Poincare/Global/CartanIsometry.lean`.

## Verified progress

The new module proves the first requested non-vacuous slice:

```lean
Poincare.CartanIsometry
  .expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
```

This states precisely that, for a common PL chart geodesic flow `α` and
linearized solution `Ψ` with initial state `(0,w)`, the derivative at `s = 0`
of

```lean
s ↦ extChartAt I x₀ (GeodesicTransport.expAt g x₀ (t • (v + s • w)))
```

is `(Ψ t).1`.  In other words, this is the chart-level form of
`D(expAt)_{t • v}(t • w) = J(t)`, with the fixed-time homogeneity carried by
the scalar `t`.

The module also combines this with the proven harmonic Jacobi uniqueness
formula:

```lean
Poincare.CartanIsometry
  .expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul
```

Under the explicit interval hypotheses that identify `Ψ` with the harmonic
Jacobi state, the derivative is rewritten as `Real.sin t • w`.

## Verification

- `lake build Poincare.Global.CartanIsometry`
- Result: build completed successfully (`Build completed successfully (3142 jobs)`).
- Forbidden-placeholder grep on `Poincare/Global/CartanIsometry.lean`: no matches.
- `git diff --check -- Poincare/Global/CartanIsometry.lean harness/reports/M5-rigid-8_blocked.md`: no issues.

## Remaining boundary

The full local-isometry packaging is still blocked.  The repo now has the
charted fixed-time derivative/Jacobi-value bridge, but I did not find an
existing nonzero-point `D(expAt)` pullback theorem that decomposes arbitrary
tangent vectors into radial and transverse parts and evaluates the metric at
`expAt x₀ v`.  The remaining missing non-vacuous glue is:

1. A pointwise radial/transverse decomposition API for tangent vectors at a
   normal-coordinate point.
2. A metric evaluation theorem for `D(expAt)` on that decomposition, including
   radial factor `1`, transverse factor `sin ‖v‖ / ‖v‖`, and zero cross terms.
3. The corresponding chain-rule assembly for `cartanMap` through the source
   exponential inverse, tangent alignment `L`, and target exponential.

Without those pieces, the requested pullback identity and local-isometry
statement would require either new assumptions or a vacuous certificate, which
the worker contract forbids.
