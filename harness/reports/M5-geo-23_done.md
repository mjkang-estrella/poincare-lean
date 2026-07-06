# M5-geo-23 done

## Deliverables

- Added `Poincare/Global/ExponentialDerivativeZero.lean`.
- Proved the Jacobi short-time position expansion for a linearized chart solution:
  - `chart_linearized_position_hasDerivAt_zero`
  - `chart_linearized_position_sub_linear_isLittleO_zero`
- Proved the zero-velocity scalar ray derivative of the charted fixed-time exponential in every direction:
  - `expAt_chart_hasDerivWithinAt_zero_smul_Ici`
  - `expAt_chart_hasDerivAt_zero_smul`
- Proved continuity at the zero velocity:
  - `expAt_continuousAt_zero`
  - `expAt_chart_continuousAt_zero`
- Isolated the remaining Fréchet upgrade as the exact velocity-variable little-o criterion:
  - `expAt_chart_hasFDerivAt_zero_of_remainder`

The unconditional Fréchet derivative is not asserted without the uniform
velocity-variable remainder.  The delivered theorem gives the requested
directional derivative in all directions plus continuity, with the Fréchet
upgrade isolated.

## Verification

Actual command run:

```bash
lake build Poincare.Global.ExponentialDerivativeZero
```

Actual result: success, `Build completed successfully (2841 jobs).`
