# M5-bridge-1 blocked

## Scope

Added `Poincare/Global/ChartCurvatureBridge.lean`.  No existing Lean source
file and no root import file was edited.

The full chart-to-manifold bridge requested in the task is not proved in this
strict partial.  I stopped before adding a theorem-shaped wrapper around the
missing dependent chart-transport curvature pushforward.

## Proved statements

Generic derivative/evaluation bridge:

```lean
theorem Poincare.ChartCurvatureBridge.fderiv_clm_family_apply
```

Raw chart curvature expansion with fixed vector evaluations pushed through
`fderiv`:

```lean
theorem Poincare.ChartCurvatureBridge.chartCurvatureOf_eq_fderiv_apply
```

Christoffel one-form symmetry as a germ, reusable for transported
Levi-Civita Christoffel fields:

```lean
theorem Poincare.ChartCurvatureBridge.eventually_christoffelOneForm_symm
```

The sharpest closed sub-bridge here: `chartCurvatureOf` rewritten into the
one-form slot convention under exactly the two needed symmetry germs:

```lean
theorem Poincare.ChartCurvatureBridge.chartCurvatureOf_eq_fderiv_apply_swapped_of_eventually_symm
```

This converts

```lean
chartCurvatureOf Γ z u v w
```

to the derivative/quadratic expression with the inner slots written as
`Γ _ w v` and `Γ _ w u`, matching the `christoffelOneForm` convention
`Γ(section, direction)`.

## Remaining blocker

The next theorem should identify the above one-form-convention expression with
the curvature operator of the model `chartLeviCivita` connection on constant
model extensions, then push that through
`chartTransportedLeviCivitaHom_inCoordinates_apply_chart` and
`chartLeviCivita_eventuallyEq_closed`.

Expected non-vacuous target shape:

```lean
chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀)
    (extChartAt I x₀ x₀) u v w
= mfderiv% (extChartAt I x₀) x₀
    (CovariantDerivative.curvatureOp g.leviCivita
      (extend E u) (extend E v) (extend E w) x₀)
```

with `u v w` expressed as tangent vectors at the chart anchor, or equivalently
with the inverse-chart derivative on the opposite side.  The obstruction is
not algebraic anymore; it is packaging the dependent tangent-space model
connection as the plain `E → E →L[ℝ] E →L[ℝ] E` family required by
`chartCurvatureOf` while keeping `FiberBundle.extend` anchored at the same
model point.

## Verification

Command run:

```bash
lake build Poincare.Global.ChartCurvatureBridge
```

Result: success.  The build completed `Poincare.Global.ChartCurvatureBridge`
and reported existing upstream linter warnings in replayed modules; there were
no warnings or errors from the new module.
