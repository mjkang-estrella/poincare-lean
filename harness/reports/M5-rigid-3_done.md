# M5-rigid-3 report: constant-curvature Jacobi seed

## Verification

- `lake build Poincare.Global.JacobiConstantCurvature`: **success**.
- The build completed with replayed upstream warnings only; the new module built.
- `rg -n "sorry|axiom|native_decide" Poincare/Global/JacobiConstantCurvature.lean`: no matches.

## Added file

- `Poincare/Global/JacobiConstantCurvature.lean`

No existing Lean file or import aggregator was edited.

## Verified signatures

```lean
theorem Poincare.hasFDerivAt_geodesicFlowField_coordinateJacobiFlowOperator
theorem Poincare.linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator
theorem Poincare.coordinateJacobiAcceleration_eq_chartCurvatureOf_remainder
def Poincare.coordinateCovariantJacobiSecond
theorem Poincare.coordinateCovariantJacobiSecond_eq_chartCurvatureOf
theorem Poincare.chartTensorKulkarniNomizu_unit_orthogonal_contraction
theorem Poincare.conformalChartMetric_chartCurvatureOf_sphereChristoffel_unit_orthogonal
theorem Poincare.chartCurvatureOf_sphereChristoffel_unit_orthogonal
def Poincare.harmonicJacobiOperator
def Poincare.jacobiSinState
theorem Poincare.jacobiSinState_hasDerivAt
theorem Poincare.jacobiSinState_uniqueOn_Icc
```

## What is proved

The new module proves that the `fderiv`-based linearized geodesic-flow operator
is the expanded coordinate Jacobi operator, so the `DΓ` and `Γ` terms in
`GeodesicLinearized.lean` are now connected to the actual derivative of the
first-order geodesic vector field.

It then records the curvature convention explicitly.  The raw coordinate
acceleration `J''` is expressed as `R(v,J)v` plus connection correction terms.
After replacing the base acceleration by the geodesic equation
`v' = -Γ(v,v)`, the chart covariant second derivative is proved equal to
`chartCurvatureOf Γ z v J v` under the standard Christoffel symmetry and
derivative-slot symmetry hypotheses.

For the stereographic round-sphere chart, the constant-curvature contraction is
proved in both lowered and vector forms.  In repository curvature slots,
unit-speed and transverse imply:

```lean
chartCurvatureOf (sphereChristoffel (E := E)) z v J v = -J
```

Finally, the sine/cosine first-order state

```lean
jacobiSinState w t = (Real.sin t • w, Real.cos t • w)
```

is proved to solve `(J,K)' = (K,-J)`, and a uniqueness wrapper is provided using
`linearODE_solution_uniqueOn_Icc`.

## Remaining boundary

This is a strict partial slice.  The module does not yet instantiate the full
manifold-side `HasConstantSectionalCurvature3` bridge along arbitrary transported
chart geodesics.  The next step is to feed the chart-curvature bridge and Gauss
orthogonality hypotheses into the covariant second-derivative theorem, then
transport the resulting oscillator statement through the existing
initial-velocity derivative machinery.
