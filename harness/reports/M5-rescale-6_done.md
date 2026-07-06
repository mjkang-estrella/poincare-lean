# M5-rescale-6 done

## Derivation

- `constSMul_metricBilinAt`: `(g.constSMul c hc).metricBilinAt x = c • g.metricBilinAt x`.
- `ricciAt`: invariant. The rescaled Levi-Civita connection agrees with the base connection by `constSMul_leviCivita_apply`, so `CovariantDerivative.ricciBilinearAt_eq_of_agree` gives the same `(0,2)` Ricci tensor.
- `ricciEndoAt`: scales by `c^-1`. The Ricci dual is invariant, but raising one index with the bilinear form `c • g.metricBilinAt x` applies the inverse Gram map, giving one factor `c^-1`.
- `scalarAt`: scales by `c^-1`. In this repo `scalarAt` is the trace of `ricciEndoAt`, so the trace of `c^-1 • Rc` is `c^-1` times the original trace.
- `ricciNormSqAt`: scales by `(c^-1)^2`. It is `trace (Rc o Rc)`, and each raised Ricci endomorphism contributes one factor `c^-1`.
- `tracelessRicciNormSqAt`: scales by `(c^-1)^2`. It is `|Ric|^2 - R^2 / n`; both terms have quadratic scaling after `R` scales by `c^-1`.

The derived constants match the expected powers.

## Final names

- `ClosedSmoothRiemannianMetric.constSMul_metricBilinAt`
- `ClosedSmoothRiemannianMetric.constSMul_ricciAt`
- `ClosedSmoothRiemannianMetric.constSMul_ricciDualAt`
- `ClosedSmoothRiemannianMetric.constSMul_ricciEndoAt`
- `ClosedSmoothRiemannianMetric.constSMul_scalarAt`
- `ClosedSmoothRiemannianMetric.constSMul_ricciNormSqAt`
- `ClosedSmoothRiemannianMetric.constSMul_tracelessRicciNormSqAt`
- `ClosedSmoothRiemannianMetric.constSMul_pinchedLimitPayload`

## Next consumers

- Pinching and normalization payloads can rewrite zero traceless-Ricci hypotheses through `constSMul_tracelessRicciNormSqAt`.
- Positive scalar hypotheses can be transported through `constSMul_scalarAt` using `inv_pos.mpr hc`.
- The hard-frozen 3D payload is packaged directly as `constSMul_pinchedLimitPayload`.

## Verification

Command:

```bash
lake build Poincare.Global.MetricRescaleCurvature
```

Result: success. The build completed successfully with existing project warnings and two nonfatal `simpa` style suggestions in the new file.
