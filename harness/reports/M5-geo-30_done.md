# M5-geo-30: done

Task: interval cutoff-one membership, length formula, and sharp distance bound.

## Delivered

Added `Poincare/Global/GeodesicLengthFinal.lean` only.  Existing source files,
including `Poincare.lean`, were not edited.

Public exports:

```lean
theorem expAt_uniform_pl_flow_cutoff_one_eq_on_Icc
```

This further shrinks the existing uniform endpoint-flow package so that PL-flow
positions remain inside the anchor cutoff-one neighborhood on the whole
`Icc (-τ) τ`.

```lean
theorem plFlowCurve_pathELength_eq
theorem expAt_pathELength_eq_chartGeodesicMetric_sqrt
```

These compute the radial curve `pathELength` on `[0, t]` from the installed
integrand identification, regularity, and constant-speed theorem.

```lean
theorem expAt_dist_le_time_mul_chartGeodesicMetric_sqrt
theorem expAt_dist_le_chartGeodesicMetric_sqrt
```

These derive the induced-distance bounds through the path-length comparison,
including the endpoint sharp chart-speed bound for small velocities.

## Verification

Forbidden-token scan on the new file:

```text
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" Poincare/Global/GeodesicLengthFinal.lean
```

Result: no matches.

Requested build:

```text
lake build Poincare.Global.GeodesicLengthFinal
```

Result:

```text
✔ [2840/2840] Built Poincare.Global.GeodesicLengthFinal (3.9s)
Build completed successfully (2840 jobs).
```

The build emitted pre-existing replay/linter warnings in dependency modules,
but no errors.
