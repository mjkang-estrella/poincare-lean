# M1-lc-regularity-5 blocked report

## Status

The target instance was not completed:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (LeviCivitaExistence.closedLeviCivitaConnection g) 1
```

No `sorry`, `axiom`, or `native_decide` was added.

Verified buildable progress was added in
`Poincare/Global/LeviCivitaRegularity.lean`, imported from `Poincare.lean`:

```lean
CovariantDerivative.chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
```

This proves the `ContMDiffAt` upgrade of
`chartTransportedLeviCivitaSection_mdiffAt_apply_chart`: if a manifold tangent
field is `C^m` at `y`, then its inverse-chart pullback is `C^m` at
`extChartAt I x0 y`.

## Verification

The new module builds:

```bash
lake build Poincare.Global.LeviCivitaRegularity
```

## What was attempted

I first tried to prove a local model-space helper in the new regularity module:

```lean
CovariantDerivative.contDiffAt_christoffel_apply_section
CovariantDerivative.modelLeviCivita_contMDiffAt
```

The proof followed `Poincare/ModelChristoffel.lean`'s global
`contDiff_christoffel_apply_section` and `modelLeviCivita_contMDiff`, replacing
global `ContDiff` hypotheses by `ContDiffAt`.

That attempt was mathematically aligned with the existing proof but did not
elaborate acceptably: Lean hit deterministic kernel/elaboration timeouts while
checking nested continuous-linear-map expressions around derivatives of the
metric-valued map. Raising instance-search heartbeats resolved the first layer
but left core `isDefEq`/tactic heartbeat failures, so the nonbuilding helper was
removed.

## Precise remaining gap

The available ingredients are now:

- model-space connection regularity:
  `CovariantDerivative.leviCivitaConnection_contMDiff`;
- chart-side connection regularity:
  `CovariantDerivative.chartLeviCivita_contMDiff`;
- smoothness of chart-transported input sections:
  `CovariantDerivative.chartTransportedLeviCivitaSection_contMDiffAt_apply_chart`;
- value identification on a cutoff-one neighborhood:
  `Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one`.

The missing bridge is a hom-bundle `EventuallyEq` statement.  For a fixed smooth
section `sigma` and each point `x0`, after choosing the cutoff-one neighborhood,
one must show that the total-space hom section

```lean
fun y => TotalSpace.mk' _ y
  ((LeviCivitaExistence.closedLeviCivitaConnection g) sigma y)
```

is eventually equal near `x0` to the chart-pushed version of the smooth
chart-side hom section coming from
`chartLeviCivita_contMDiff`.

The existing identification theorem only gives equality after applying the
hom to a tangent vector:

```lean
chartTransportedLeviCivitaValueAt ... sigma hy v =
  (LeviCivitaExistence.closedLeviCivitaConnection g) sigma y v
```

To finish the instance, this value equality must be converted into equality of
dependent continuous linear maps in the tangent hom bundle, with the chart
coordinates/trivializations reduced to the corresponding model-space
continuous-linear-map expression. Once this eventual equality is available,
`ContMDiffAt.congr_of_eventuallyEq` and the class's `contMDiff` field should
finish the local-to-global gluing.

