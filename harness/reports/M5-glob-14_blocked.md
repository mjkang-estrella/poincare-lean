# M5-glob-14 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/TransportedCompatibility.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one
```

## Proved strict partial

The theorem proves the cutoff-one blended metric transition law on an honest
chart overlap:

```text
G¹(σ z)(Dσ u, Dσ w) = G⁰(z)(u, w)
```

in the repo's actual API shape:

```text
chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
  (chartTransitionDeriv x₀ y₀ z u)
  (chartTransitionDeriv x₀ y₀ z w)
=
chartGeodesicMetric g x₀ z u w
```

under the necessary hypotheses that:

- `z` lies in the `x₀` chart target;
- `(extChartAt I x₀).symm z` lies in the `y₀` chart source;
- both blending cutoffs are `1` at the source and target chart points.

The proof is non-vacuous and uses the existing definitional chart-metric
transition law:

```lean
chartMetric_chartTransitionDeriv
```

plus the cutoff-one rewrite:

```lean
blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
```

This records the requested pullback metric law for the blended geodesic
metrics in the only form that can be globally true: with explicit cutoff-one
assumptions.

## Remaining blockers

The full transported compatibility identity was not proved in this task.

1. The differentiated version of the pullback metric law still needs to be
   packaged so that the derivative of
   `G¹(σ z)(Dσ u, Dσ w)` is converted into the exact target
   `chartChristoffelField_pairing_eq_blendedChartMetric` shape.

2. The chain-rule expansion still needs to turn the source Christoffel
   pairing terms into the transported target Christoffel terms plus the
   ordinary second-derivative correction with the minus-sign convention from
   `TransitionLaw.lean`.

3. The inverse target-coordinate packaging is still needed: velocities stated
   as target coordinates must be pulled back through the chart transition
   inverse before applying the source-coordinate transition formula.

4. The velocity-component chain-rule producer consumed by
   `ChristoffelTransition.lean` remains unproduced from the abstract law.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/TransportedCompatibility.lean
git diff --check -- Poincare/Global/TransportedCompatibility.lean
lake build Poincare.Global.TransportedCompatibility
```

Actual result:

```text
rg: no matches
git diff --check: no output
lake build Poincare.Global.TransportedCompatibility
✔ [2831/2831] Built Poincare.Global.TransportedCompatibility (2.4s)
Build completed successfully (2831 jobs).
```

The build replayed pre-existing imported-module warnings; the new module
itself built successfully and introduced no reported warning.
