# M5-model-6 done

## Scope

Added `Poincare/Global/ConformalCurvature.lean`.  No existing Lean source file or
root import file was edited.

## Curvature convention

I checked the existing curvature surfaces before introducing the chart-level
definition:

- `Poincare/RiemannCurvatureOperator.lean` defines the repository orientation
  `R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z`.
- `Poincare/ModelChristoffel.lean` proves
  `CovariantDerivative.curvatureOp_modelLeviCivita_extend`, which has the same
  first-two-slot orientation on constant model vector fields.
- I did not find an existing chart-level curvature-from-Christoffel definition
  with these conventions, so the new file defines `chartCurvatureOf`.

For constant chart vector fields `u`, `v`, `w`, the bracket term vanishes and
the chart connection has `nabla_u w = Gamma(z) u w`.  Thus

```lean
chartCurvatureOf Gamma z u v w
  = (fderiv R Gamma z u) v w - (fderiv R Gamma z v) u w
    + Gamma z u (Gamma z v w) - Gamma z v (Gamma z u w)
```

This is the `R(u,v)w` orientation matching `CovariantDerivative.curvatureOp`.

The slot convention from `M5-model-5` is respected: the chart Christoffel slots
are the classical `Gamma(u,v)` slots, while the earlier one-form API flips slots
only at the `christoffelOneForm` boundary.

## Final signatures

Main definitions:

```lean
def chartCurvatureOf (Gamma : E -> E ->L[R] E ->L[R] E)
    (z : E) (u v w : E) : E

def chartTensorKulkarniNomizu
    (h k : E -> E -> R) (u v w a : E) : R

def conformalChartMetricForm (f : E -> R) (z : E) (u v : E) : R
```

Sphere Christoffel data:

```lean
def sphereChristoffelCoeff (z : E) : R := 2 / (||z|| ^ 2 + 4)

def sphereChristoffelCoreFormula (z u v : E) : E :=
  <u,v> z - <z,u> v - <z,v> u

def sphereChristoffel : E -> E ->L[R] E ->L[R] E
```

Derivative and curvature theorems:

```lean
theorem hasFDerivAt_sphereChristoffelCoeff
theorem fderiv_sphereChristoffelCoeff
theorem hasFDerivAt_sphereChristoffel
theorem fderiv_sphereChristoffel

theorem chartCurvatureOf_sphereChristoffel_eq
theorem inner_chartCurvatureOf_sphereChristoffel
theorem conformalChartMetric_chartCurvatureOf_sphereChristoffel
```

The vector curvature identity proved is:

```lean
chartCurvatureOf sphereChristoffel z u v w
  = stereoInvFunAuxConformalFactor z •
      (inner R v w • u - inner R u w • v)
```

After lowering with the conformal chart metric
`G z u v = stereoInvFunAuxConformalFactor z * inner R u v`, the chart-level
constant-curvature form is:

```lean
G z (chartCurvatureOf sphereChristoffel z u v w) a
  = -(1 / 2) *
      chartTensorKulkarniNomizu (G z) (G z) u v w a
```

This matches `HasConstantSectionalCurvature3` with `kappa = 1`.

## General conformal formula note

The general positive `C^2` conformal curvature formula was not introduced as a
separate theorem.  I specialized the computation to the frozen sphere factor,
which was the required deliverable, because the current API friction is in the
function-space derivative layer.  The new file still exposes the reusable
chart operator, Kulkarni-Nomizu chart form, and a fully proved concrete
Christoffel derivative for the stereographic sphere factor.

## Transport roadmap

The next manifold-level task should connect this chart computation to
`roundSphereMetric3` by:

1. Reusing `RoundSphereChartMetric.lean` to identify the metric coefficients of
   `roundSphereMetric3` in the stereographic chart with
   `stereoInvFunAuxConformalFactor z * inner R _ _`.
2. Using the existing conformal Christoffel bridge from
   `ConformalChristoffel.lean` to identify the transported Levi-Civita
   Christoffel field with `sphereChristoffel`.
3. Applying the constant-vector chart derivation behind
   `chartCurvatureOf` and the repository bridge
   `curvatureOp_modelLeviCivita_extend`/transport lemmas to rewrite the
   manifold `curvatureOp` in chart coordinates.
4. Reusing `conformalChartMetric_chartCurvatureOf_sphereChristoffel` to close
   the `HasConstantSectionalCurvature3` target for `roundSphereMetric3` with
   `kappa = 1`.

## Verification

Command run:

```bash
lake build Poincare.Global.ConformalCurvature
```

Result: success.  Lean built `Poincare.Global.ConformalCurvature`; only linter
warnings were reported, with no errors.
