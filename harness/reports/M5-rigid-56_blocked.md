# M5-rigid-56 blocked: corrected coordinate state is not the abstract harmonic state

## Status

Added `Poincare/Global/PositionBridge.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The requested vector endpoint formula was not proved.  The new module exports
one non-vacuous boundary theorem:

```lean
Poincare.PositionBridge.correctedCoordinateState_hasDerivAt
```

It replays the cutoff-one constant-curvature and linearized-flow bookkeeping
from the `JacobiNormClose` / `CartanIsometryTheorem` route and proves the exact
plain-coordinate derivative of the corrected state.

## Verified payload

For a hosted chart-linearized state `Ψ = (J,K)` along a chart geodesic `γ`, set

```lean
D t = K t + Γ (γ t).1 (γ t).2 (J t)
```

where `Γ = GeodesicTransport.chartChristoffelField g x₀`.  Under the usual
cutoff-one, target, unit-speed, transverse, constant-curvature, geodesic, and
linearized-flow hypotheses, the new theorem proves

```lean
HasDerivAt (fun τ => (J τ, D τ))
  (D t - Γ (z t) (V t) (J t),
    -J t - Γ (z t) (V t) (D t)) t
```

This is the honest covariant-coordinate first-order system:

```text
J' = D - Γ(V,J)
D' = -J - Γ(V,D)
```

The theorem uses the same pointwise oscillator discharge as the scalar norm
route:

```lean
coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
```

so the obstruction is not a missing curvature fact.

## Blocker

`jacobi_position_eq_sin_smul_on_Icc` consumes an abstract harmonic state whose
ordinary derivative is

```lean
harmonicJacobiOperator (J, D) = (D, -J)
```

The corrected chart-coordinate state has the same position component `J =
Ψ.1`, but its ordinary chart derivative has the two Christoffel terms displayed
above.  Therefore the current repo API still does not supply the required
parallel-frame or covariant-state identification that would turn the
covariant-coordinate system into the abstract harmonic state while preserving
the hosted position component.

Consequently the missing endpoint bridge remains:

```lean
(Ψ w T).1 =
  Real.sin (speed * T) • ((speed * T)⁻¹ • w)
```

or equivalently the `hostedTransverseScaleFromSpeed` form needed by
`PositionRoute`.  Feeding `PositionRoute.lean` onward would still require
assuming this endpoint equality, so I stopped at the verified boundary instead
of adding a vacuous wrapper.

## Verification

Reserved-token scan on the new Lean file:

```bash
rg -n "\\b(sorry|admit|axiom|native_decide)\\b" Poincare/Global/PositionBridge.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\\s" \
  Poincare/Global/PositionBridge.lean
```

Actual result:

```text
49:theorem correctedCoordinateState_hasDerivAt
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/PositionBridge.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.PositionBridge
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3150/3150] Built Poincare.Global.PositionBridge (6.8s)
Build completed successfully (3150 jobs).
```
