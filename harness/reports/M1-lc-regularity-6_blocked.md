# M1-lc-regularity-6 blocked report

## Status

The target instance was not completed:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (LeviCivitaExistence.closedLeviCivitaConnection g) 1
```

No `sorry`, `axiom`, or `native_decide` was added.

The obstruction isolated in `M1-lc-regularity-5_blocked.md` was closed.  The
pointwise applied equality on the cutoff-one neighborhood is now lifted to
equality of the dependent continuous linear maps, and then to a total-space
hom-bundle `Filter.EventuallyEq`.

Verified buildable progress was added in
`Poincare/Global/LeviCivitaRegularity.lean`:

```lean
CovariantDerivative.chartTransportedLeviCivitaHom
CovariantDerivative.chartTransportedLeviCivitaHom_apply
CovariantDerivative.chartTransportedLeviCivitaHom_inCoordinates_apply_chart
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed
```

## Verification

The updated module builds:

```bash
lake build Poincare.Global.LeviCivitaRegularity
```

The verified commits are:

```text
bf4bb66f Add chart transported Levi-Civita hom helper
cafbed3b Bridge transported Levi-Civita hom to closed connection
4bc863cb Add hom-bundle eventual equality bridge
b708d2ca Normalize transported Levi-Civita hom coordinates
```

## What was completed

The new chart-transported hom helper packages the chart-side Levi-Civita
connection value as a dependent tangent-fiber continuous linear map:

```lean
CovariantDerivative.chartTransportedLeviCivitaHom
```

Its application lemma reduces the packaged hom to the previously existing
chart-transported value:

```lean
CovariantDerivative.chartTransportedLeviCivitaHom_apply
```

The core bridge from the previous report is:

```lean
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
```

For `y` in the cutoff-one chart neighborhood, this theorem proves equality of
the dependent continuous linear maps

```lean
CovariantDerivative.chartTransportedLeviCivitaHom ... sigma y =
  (LeviCivitaExistence.closedLeviCivitaConnection g) sigma y
```

by extensionality over tangent vectors and the existing value-level theorem

```lean
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
```

This is lifted to the total-space hom section as:

```lean
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed
```

Finally, the coordinate-normalization lemma identifies the chart-transported
hom in tangent-bundle coordinates with the model chart-side Levi-Civita hom:

```lean
CovariantDerivative.chartTransportedLeviCivitaHom_inCoordinates_apply_chart
```

Concretely, for `hy : y in (extChartAt I x0).source`, it rewrites

```lean
ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
  x0 y x0 y (chartTransportedLeviCivitaHom ... sigma y)
```

to

```lean
(chartLeviCivita ...)(chartTransportedLeviCivitaSection x0 sigma)
  (extChartAt I x0 y)
```

using the tangent-bundle trivialization identities and the round-trip
`mfderiv` identity for `extChartAt`.

## Precise remaining gap

The old hom-bundle `EventuallyEq` gap is no longer the blocker.  The remaining
step is the local regularity side needed before the final `EventuallyEq` gluing:

```lean
ContMDiffAt
  (𝓘(𝕜, M))
  (Bundle.TotalSpace.toChartedSpace ...)
  1
  (fun y =>
    (⟨y, CovariantDerivative.chartTransportedLeviCivitaHom ... sigma y⟩ :
      TotalSpace (E ->L[ℝ] E) (fun y : M => TM y ->L[ℝ] TM y)))
  x0
```

The coordinate lemma above reduces this to local smoothness of the model
chart-side hom

```lean
fun z =>
  (chartLeviCivita ...)(chartTransportedLeviCivitaSection x0 sigma) z
```

near `extChartAt I x0 y`.  The available global theorem

```lean
CovariantDerivative.chartLeviCivita_contMDiff
```

requires a globally smooth model section, while

```lean
CovariantDerivative.chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
```

currently gives only the needed local `ContMDiffAt` regularity of
`chartTransportedLeviCivitaSection x0 sigma`.

The likely next proof is the same localization pattern used in
`Poincare/LocalConnectionRegularity.lean`:

1. Convert the local `ContMDiffAt` of the chart-transported section to
   `ContMDiffOn` on a neighborhood.
2. Choose a smooth bump equal to `1` near the chart point with support inside
   that neighborhood.
3. Globalize the local section as `tau := psi • chartTransportedLeviCivitaSection x0 sigma`
   using `ContMDiffOn.smul_section_of_tsupport`.
4. Apply `CovariantDerivative.chartLeviCivita_contMDiff` to `tau`.
5. Use covariant-derivative germ locality to transfer regularity from `tau`
   back to `chartTransportedLeviCivitaSection x0 sigma` near the chart point.
6. Compose with `extChartAt`, use
   `CovariantDerivative.chartTransportedLeviCivitaHom_inCoordinates_apply_chart`,
   then use
   `Poincare.LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed`
   and `ContMDiffAt.congr_of_eventuallyEq` to prove the closed connection hom
   section is `ContMDiffAt`.
7. Generalize over `x0` to fill the class field and then expose the goal
   instance/theorem.

