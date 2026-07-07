# M5-glob-18 done report

## Status

Done in a new Lean file only:
`Poincare/Global/TransitionLawFires.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
```

## Proved

On a local cutoff-one chart overlap, the target chart Christoffel field equals
the signed transport of the source chart Christoffel field:

```text
Gamma_y(sigma z)(Dsigma u)(Dsigma v)
  = Dsigma(Gamma_x(z)(u,v)) - D2sigma(z)(u,v).
```

The proof combines:

- the concrete differentiated pullback law from
  `chartGeodesicMetric_differentiated_pullback_hdiff_of_eventually_cutoff_eq_one`;
- the transported Koszul pairing identity from
  `chartGeodesicMetric_transportedChristoffel_pairing_eq_of_differentiated_pullback`;
- the target chart Christoffel pairing identity
  `chartChristoffelField_pairing_eq_blendedChartMetric`;
- invertibility of the chart-transition derivative on the honest overlap via
  `chartTransitionDeriv_eq_chartTransitionMFDeriv` and the existing chart
  derivative invertibility facts;
- nondegeneracy of the target blended chart metric through
  `CovariantDerivative.chartBilin_nondegenerate`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|axiom|native_decide)\b' Poincare/Global/TransitionLawFires.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/TransitionLawFires.lean
lake build Poincare.Global.TransitionLawFires
```

Actual result:

```text
rg placeholder scan: no matches
top-level declaration scan:
35:theorem chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one

lake build Poincare.Global.TransitionLawFires
[2836/2836] Built Poincare.Global.TransitionLawFires (3.2s)
Build completed successfully (2836 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
