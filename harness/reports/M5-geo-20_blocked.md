# M5-geo-20 blocked

## Files

- Added `Poincare/Global/GeodesicDerivativeFinal.lean`.
- Added this report.
- No existing Lean module, root import file, or harness task file was edited.

## Lean payload

The new module proves the verified Gronwall comparison layer for the residual
argument.

- `gronwall_residual_norm_le`: applies Mathlib's
  `norm_le_gronwallBound_of_norm_deriv_right_le` to a residual curve with
  zero initial residual and a nonhomogeneous derivative bound.
- `gronwallBound_zero_left_mul`: records linearity of the zero-initial
  Gronwall bound in the driving term.
- `residual_derivative_norm_bound_of_taylor_remainder`: proves the algebraic
  split
  `F q - F gamma - s • A psi =
   (F q - F gamma - A (q - gamma)) + A (q - gamma - s • psi)`,
  turning a Taylor remainder estimate plus a linearized-operator norm bound
  into the derivative inequality consumed by Gronwall.
- `residual_uniform_isLittleO_on_Icc_of_gronwall_bound`: if the residual
  derivative bound has arbitrarily small `eta * ‖s‖` driving coefficient
  eventually in `s`, then uniformly for `t in Icc 0 T`,
  `‖R s t‖ ≤ epsilon * ‖s‖` eventually in `s`.
- `initialVelocityResidual` and the three `initialVelocity...` theorems:
  specialize the comparison spelling to
  `alpha (z0, v + s • w) t - alpha (z0, v) t - s • Psi t`, extract the
  fixed-time little-o statement, and derive
  `HasDerivAt (fun s => alpha (z0, v + s • w) t) (Psi t) 0`.

Spelling adaptation: the schematic function-valued little-o from
`M5-geo-19_blocked.md` does not type directly because this Lean environment has
no normed-group instance for the full function space `R -> X`. The module uses
the equivalent interval-uniform estimate:
`forall epsilon > 0, eventually in s, forall t in Icc 0 T,
  ‖R s t‖ <= epsilon * ‖s‖`.

## Blocker

One statement remains: for the actual uniform PL geodesic flow `alpha` and
linearized solution `Psi`, instantiate the residual hypotheses of
`initialVelocityResidual_uniform_isLittleO_on_Icc_of_gronwall_bound` by proving
eventual continuity, the within-interval derivative of `R(s, t)`, zero initial
residual, and the derivative inequality
`‖R'_s(t)‖ <= K * ‖R(s, t)‖ + eta * ‖s‖` from the existing compact-tube uniform
Taylor remainder plus Lipschitz dependence.

## Verification

Forbidden-token scan of the new Lean file: no matches.

Command run:

```bash
lake build Poincare.Global.GeodesicDerivativeFinal
```

Actual result:

```text
Built Poincare.Global.GeodesicDerivativeFinal (2.5s)
Build completed successfully (2834 jobs).
```

The build replayed existing upstream warnings; it emitted no diagnostics from
`Poincare/Global/GeodesicDerivativeFinal.lean`.
