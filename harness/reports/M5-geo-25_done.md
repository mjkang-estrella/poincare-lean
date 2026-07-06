# M5-geo-25 done

## Deliverables

- Added `Poincare/Global/ExponentialFrechet.lean`.
- Proved the uniform velocity-variable remainder in the exact shape required by
  `expAt_chart_hasFDerivAt_zero_of_remainder`:
  - `flow_velocity_sub_initial_norm_le_of_accel_bound`
  - `flow_position_sub_linear_norm_le_of_accel_bound`
  - `expAt_chart_remainder_isLittleO_zero`
- Proved the Fréchet derivative of the charted fixed-time exponential at zero:
  - `expAt_chart_hasFDerivAt_zero`

## Spelling adaptations

The geo-23 criterion asks for
`extChartAt I x₀ (expAt g x₀ v) - (extChartAt I x₀ x₀ + v) = o(v)`.
The proof obtains this by using the closed-interval PL-flow identity for
`expAt (t • u)`, with `‖u‖ = δ / 2`, and a compact acceleration bound on the
common closed flow tube.  Two one-dimensional mean-value estimates give the
uniform short-time position remainder `z(t) - (z₀ + t • u) = O(T * t)`;
shrinking the common time horizon `T` gives the required velocity-variable
little-o.

## Local-injectivity payoff

The derivative-at-zero statement is now available.  I did not force an inverse
function theorem corollary: the Mathlib inverse-function interfaces require
stronger local regularity such as `ContDiffAt`/strict derivative data, and this
task only establishes the `HasFDerivAt` endpoint.

## Verification

Actual command run:

```bash
lake build Poincare.Global.ExponentialFrechet
```

Actual result: success, `Build completed successfully (2842 jobs).`
