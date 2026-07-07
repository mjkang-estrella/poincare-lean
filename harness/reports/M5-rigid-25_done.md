# M5-rigid-25 done: chart state feeds the Jacobi norm system

## Files

- Added `Poincare/Global/JacobiNormClose.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Verified strict partial

The new module contains one isolated non-vacuous statement:

```lean
theorem Poincare.JacobiNormClose.chart_linearized_state_feeds_norm_system_at
```

This proves the pointwise state-identification and norm-system input bridge.
Given:

- a genuine chart geodesic state `gamma`,
- a genuine chart-linearized state `Psi = (J,K)`,
- cutoff-one, unit-speed, transverse constant-curvature data at the same state,
- differentiability of the endpoint chart metric at the base chart point,

the theorem defines the corrected covariant first derivative

```lean
D tau = K tau + Gamma (z tau) (V tau) (J tau)
```

and proves that `normA`, `normB`, and `normC` satisfy the closed scalar system
at `t`:

```lean
a' = 2 * b
b' = c - a
c' = -2 * b
```

The proof uses the existing first-component mixed derivative
`chart_linearized_fst_hasDerivAt`, identifies the second component through
`linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator`, computes the
covariant correction derivative, applies
`coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`, and
then feeds the resulting `J'`/`D'` hypotheses into `JacobiNormSystem`.

## Remaining boundary

This does not yet package ODE uniqueness into
`a(t) = sin t ^ 2 * |w|^2`, nor does it polarize that identity into the full
exp-chart coefficient formulas or the final local-isometry theorem.  Those are
now downstream coefficient-assembly steps: the chart-linearized state and the
covariant norm system are connected at the pointwise input level.

## Verification

Forbidden-placeholder scan on `Poincare/Global/JacobiNormClose.lean` found no
matches.

Required build:

```bash
lake build Poincare.Global.JacobiNormClose
```

Actual result: success. Final output ended with:

```text
✔ [3149/3149] Built Poincare.Global.JacobiNormClose (6.2s)
Build completed successfully (3149 jobs).
```

The build replayed existing upstream warnings; it emitted no errors from the
new module.
