# M5-rigid-79 done report

## Status

Added `Poincare/Global/OneSidedPayload.lean` as a new module.  No existing
Lean files were edited, including `Poincare.lean`.

The module provides the one-sided integrated transverse Gauss payload on
`Icc 0 T`, replacing the old open-interval time-derivative requirements with
`HasDerivWithinAt ... (Icc 0 T)` hypotheses.

## Verified payload

New low-level within-derivative adapters:

```lean
Poincare.GeodesicTransport.geodesic_position_hasDerivWithinAt
Poincare.GeodesicTransport.geodesic_velocity_hasDerivWithinAt
Poincare.GeodesicTransport.chart_linearized_fst_hasDerivWithinAt
Poincare.GeodesicTransport.chart_geodesic_transverse_pairing_hasDerivWithinAt
```

New one-sided integration bridge:

```lean
Poincare.GeodesicTransport.chart_initialVelocity_transverse_pairing_hasDerivWithinAt_initialSlope
Poincare.GeodesicTransport.chart_initialVelocity_transverse_pairing_eq_t_mul_initial_on_Icc
Poincare.GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_oneSided
Poincare.GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
```

New source/target orthogonality feeds:

```lean
Poincare.OrthogonalityFeed.chartMetric_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
Poincare.OrthogonalityFeed.source_transverse_horth_on_Icc_of_oneSided_payload
Poincare.OrthogonalityFeed.target_transverse_horth_on_Icc_of_oneSided_payload
```

These consume `hflow` only for times in `Icc 0 T`, so the existing one-sided
fixed-time variation exports can feed this payload directly.  The scalar
integration step uses convexity of `Icc 0 T` and `fderivWithin = 0`, not an
open interval around `0`.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/OneSidedPayload.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/OneSidedPayload.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.OneSidedPayload
```

Actual result: succeeded.  The build emitted pre-existing warnings from
imported modules, but no warning from `Poincare/Global/OneSidedPayload.lean`.
Final build lines:

```text
✔ [3182/3182] Built Poincare.Global.OneSidedPayload (6.4s)
Build completed successfully (3182 jobs).
```
