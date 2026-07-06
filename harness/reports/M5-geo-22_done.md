# M5-geo-22 done

## Files

- Added `Poincare/Global/GaussLemmaIntegrated.lean`.
- Added this report.
- Did not edit existing Lean modules, `Poincare.lean`, or harness task files.

## Lean payload

The new module integrates the previously proved transverse ingredients for the
radial initial-velocity family `s ↦ α (z₀, v + s • w)`.

- `chart_linearizedGeodesicFlowFieldAlong_fst` and
  `chart_linearized_fst_hasDerivAt` project the chart linearized system to
  `J' = K`.
- `chart_initialVelocity_speed_hasDerivAt_of_flowDerivative` differentiates
  `s ↦ G(α_s t)(α_s' t, α_s' t)` at `s = 0` using the full-state flow
  derivative and metric chain rule.
- `chart_initialVelocity_speed_hasDerivAt_of_uniform_geodesicFlow` specializes
  that derivative to the uniform flow theorem from
  `GeodesicFlowDerivative.lean`.
- `chart_initialVelocity_initialSpeed_hasDerivAt` proves the initial-speed
  derivative
  `d/ds|₀ G(z₀)(v + s • w, v + s • w) =
    G(z₀)(w, v) + G(z₀)(v, w)`.
- `chart_initialVelocity_speed_eventuallyEq_initialSpeed_of_constantSpeed`
  uses constant speed for each geodesic to identify the fixed-time speed with
  the initial speed as an eventual equality in `s`.
- `chart_initialVelocity_transverse_pairing_hasDerivAt_initialSlope` combines
  the pointwise transverse identity, the flow derivative, and constant speed to
  prove
  `d/dt G(γ t)(J t, γ' t) = G(z₀)(v, w)`.
- `chart_initialVelocity_transverse_pairing_eq_t_mul_initial` integrates that
  constant-slope scalar ODE on a connected open interval.  Because this is the
  radial initial-velocity variation, `Ψ 0 = (0, w)`, so the exact law is
  `G(γ t)(J t, γ' t) = t * G(z₀)(v, w)`.
- `chart_initialVelocity_integrated_transverse_gauss_orthogonal` is the chart
  Gauss lemma corollary:
  `G(z₀)(v, w) = 0 ⟹ G(γ t)(J t, γ' t) = 0`.

The exact integrated law has no constant `G(z₀)(w, v)` term for this radial
initial-velocity variation: the Jacobi position component starts at zero, while
the velocity component starts at `w`.

## Verification

Forbidden-token scan of `Poincare/Global/GaussLemmaIntegrated.lean`:
actual result was no matches.

Required build:

```bash
lake build Poincare.Global.GaussLemmaIntegrated
```

Actual result:

```text
✔ [2840/2840] Built Poincare.Global.GaussLemmaIntegrated (3.8s)
Build completed successfully (2840 jobs).
```

The build replayed existing upstream warnings; it emitted no diagnostics from
`Poincare/Global/GaussLemmaIntegrated.lean`.
