# M5-rigid-18 done: smooth-dependence payload discharged from flow derivative

## Files

- Added `Poincare/Global/SmoothDependenceDischarge.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Payload map

The new module records the de-facto payload that `GaussLemmaTransverse` and the
integrated transverse Gauss assembly consume, without changing the old
`ChartGeodesicInitialVelocitySmoothDependence` definition.

Proved bridge lemmas:

```lean
theorem Poincare.GeodesicTransport.chart_initialVelocity_fixedTime_payload_of_uniform_geodesicFlow
```

This discharges the fixed-time variation fields from
`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`:

- whole-state derivative:
  `HasDerivAt (fun s => α (z₀, v + s • w) t) (Ψ t) 0`
- position component:
  `HasDerivAt (fun s => (α (z₀, v + s • w) t).1) (Ψ t).1 0`
- velocity component:
  `HasDerivAt (fun s => (α (z₀, v + s • w) t).2) (Ψ t).2 0`

```lean
theorem Poincare.GeodesicTransport.chart_initialVelocity_mixedDerivative_payload_of_linearized
```

This discharges mixed-derivative commutation from the first component of the
linearized ODE:

```lean
HasDerivAt (fun τ => (Ψ τ).1) (Ψ t).2 t
```

That is exactly `J' = K`, using `chart_linearized_fst_hasDerivAt`.

```lean
theorem Poincare.GeodesicTransport.chart_initialVelocity_transverse_variation_identity_of_uniform_geodesicFlow
```

This combines the fixed-time payload, the mixed-derivative payload, and
`chart_geodesic_transverse_variation_identity` to produce the pointwise
transverse Gauss identity at `s = 0`.

```lean
theorem Poincare.GeodesicTransport.exists_uniform_chart_initialVelocity_payload_package
```

This is the named discharge-package entrypoint: it starts from the exported
uniform PL chart flow behind `expAt_uniform_pl_flow_eq_on_Icc` and packages the
common flow plus the pointwise payload identity for every compatible linearized
solution `Ψ`.

```lean
theorem Poincare.GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_payload
```

This records the integrated transverse Gauss law with its interval-scoped
payload hypotheses spelled explicitly, delegating to the existing
`chart_initialVelocity_integrated_transverse_gauss`.

## Endpoint assembly boundary

I did not add the full endpoint Jacobi-pairing/source-weight identity.  The
remaining obstruction is not the old smooth-dependence placeholder anymore:
the fixed-time and mixed-derivative pieces are now discharged from the proven
flow derivative.  The remaining assembly still needs a single synchronized
interval package combining:

- the positive-time fixed-time derivative theorem,
- the open-interval integrated Gauss hypotheses around `0`,
- the constant-curvature Jacobi oscillator hypotheses,
- endpoint chart-target and cutoff-one data.

In particular, the current proven flow derivative is exported for
`t ∈ Icc 0 ε`, while the existing integrated theorem is stated on an open
interval `Ioo a b` containing `0` and therefore asks for its hypotheses on both
sides of `0`.  Bridging that mismatch should be a separate interval-packaging
lemma rather than a vacuous endpoint wrapper.

## Verification

Forbidden-token check:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/SmoothDependenceDischarge.lean
```

Actual result: no matches.

Required build:

```bash
lake build Poincare.Global.SmoothDependenceDischarge
```

Actual result: success. Final output ended with:

```text
✔ [2841/2841] Built Poincare.Global.SmoothDependenceDischarge (3.5s)
Build completed successfully (2841 jobs).
```

The build replayed existing upstream warnings; it emitted no errors from the
new module.
