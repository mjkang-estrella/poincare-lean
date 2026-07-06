# M5-geo-21 done

## Files

- Added `Poincare/Global/GeodesicFlowDerivative.lean`.
- Added this report.
- No existing Lean module, `Poincare.lean`, or harness task file was edited.

## Lean payload

The new module instantiates the residual Gronwall layer from
`Poincare.Global.GeodesicDerivativeFinal` for the uniform chart geodesic flow.

- `initialVelocityResidualDeriv`: the time-derivative candidate for
  `α(z₀, v + s • w) t - α(z₀, v) t - s • Ψ t`.
- `initialVelocityResidual_hasDerivWithinAt_of_flow_linearized`: differentiates
  the residual from the two nonlinear flow ODEs and the linearized equation.
- `eventually_const_mul_norm_le_nhds_zero`,
  `closedBall_radius_add_one_mem_nhds`, and
  `eventually_norm_add_smul_lt`: small analytic helpers used to turn fixed-time
  Lipschitz dependence into the eventual compact-tube Taylor hypothesis.
- `GeodesicTransport.chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`:
  for a common PL chart flow `α`, a base velocity `v`, direction `w`, and a
  linearized solution `Ψ` on the same interval, proves

```lean
HasDerivAt
  (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
  (Ψ t) 0
```

The proof discharges the abstract hypotheses by:

- deriving residual continuity and right-time derivatives from the ODEs on
  `Icc (-ε) ε`;
- proving zero initial residual from the PL initial condition and `Ψ 0 = (0,w)`;
- widening the common PL ball by `+ 1` so the closed ball is a neighborhood of
  each base state, allowing `norm_fderiv_le_of_lipschitzOn`;
- applying the compact-uniform Taylor remainder on that widened ball;
- using `chart_flow_initialVelocity_lipschitzOn_of_ODE` to bound
  `‖α(z₀,v+s•w)τ - α(z₀,v)τ‖` by `O(‖s‖)`;
- feeding the resulting derivative inequality into
  `initialVelocity_hasDerivAt_of_gronwall_residual_bound`.

## Transverse Gauss glue

Not added here.  `GaussLemmaTransverse.lean` still expects the stronger
two-variable smooth-dependence interface, especially fixed-time component
`s`-derivatives and the mixed derivative `∂ₜ J = K`.  This task proves the
fixed-time full-state flow derivative supplied by the linearized solution; a
separate bridge should package its first and second components plus the
time-derivative relation into that transverse interface.

## Verification

Forbidden-token scan of the new Lean file:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/GeodesicFlowDerivative.lean
```

Actual result: no matches.

Required build:

```bash
lake build Poincare.Global.GeodesicFlowDerivative
```

Actual result:

```text
✔ [2835/2835] Built Poincare.Global.GeodesicFlowDerivative (5.0s)
Build completed successfully (2835 jobs).
```

The build replayed existing upstream warnings; it emitted no diagnostics from
`Poincare/Global/GeodesicFlowDerivative.lean`.
