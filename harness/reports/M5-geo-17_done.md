# M5-geo-17 done

## Files

- Added `Poincare/Global/GeodesicDependence.lean`.
- Added this report.
- No existing Lean file, root import file, or harness input file was edited.

## Lean payload

The new module proves the first quantitative dependence layer, not full
velocity differentiability.

- `chartChristoffelField_contDiffAt_base` and `chartChristoffelField_contDiff`:
  the chart Christoffel field is globally `C1` in model coordinates.
- `geodesicFlowField_chartChristoffelField_contDiff`: the first-order chart
  geodesic flow field is globally `C1`.
- `geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall`: on every
  closed ball in chart state space, the first-order flow field has some finite
  Lipschitz constant `K : NNReal`.
- `chart_flow_initialVelocity_lipschitzOn_of_ODE`: for any common PL chart
  flow that stays in the same closed ball on `[-epsilon, epsilon]`, Gronwall
  gives fixed-time Lipschitz dependence on initial velocity:
  `v |-> alpha (z0, v) t` is `LipschitzOnWith exp (K * epsilon)` on
  `ball 0 delta` for every `t in Icc 0 epsilon`.
- `exists_uniform_local_geodesic_chart_flow_lipschitzOn_initialVelocity`:
  packages the existing endpoint-controlled PL flow with the above Lipschitz
  estimate.
- `exists_uniform_local_geodesic_chart_flow_initialVelocity_continuousOn`:
  continuity of the chart flow time slices follows from the Lipschitz estimate.
- `expAt_continuousOn_smallBall`: `expAt g x0` is continuous on a sufficiently
  small velocity ball. The proof uses `eta = min tau epsilon / 2`, because the
  exported endpoint/ray interface gives separate positive `tau` and `epsilon`
  without a direct ordering between them.

## What remains for full differentiability

The next real step is the linearized-equation comparison. A useful target is:

- define finite difference quotients
  `s^-1 * (alpha (z0, v + s * w) t - alpha (z0, v) t)` on the same PL interval;
- prove uniform boundedness and equicontinuity using the Lipschitz result here
  plus the `C1` field estimates;
- show convergence to the variational equation
  `Psi' t = fderiv R F (alpha (z0, v) t) (Psi t)`,
  with `Psi 0 = (0, w)`;
- use uniqueness for that linearized equation on the common interval;
- export fixed-time differentiability in `v`, then split `Psi` into the Jacobi
  position and velocity components needed by the transverse Gauss bridge.

I did not add a Jacobi convergence theorem statement, since the convergence
proof was not completed here and a bare statement would not move the verified
interface forward.

## Refined interface proposal

Keep the current `ChartGeodesicInitialVelocitySmoothDependence` target as the
end interface, but insert a quantitative dependency package below it:

- common PL data: `delta`, `epsilon`, `alpha`, initial condition, ODE law, and
  closed-ball containment;
- fixed-time initial-velocity Lipschitz estimate with constant
  `exp (K * epsilon)`;
- variational payload, once proved: for each `v,w`, a curve `Psi` with
  `Psi 0 = (0,w)`, ODE
  `Psi' t = fderiv R F (alpha (z0,v) t) (Psi t)`, and
  `HasDerivAt (fun s => alpha (z0, v + s * w) t) (Psi t) 0`.

Then the Gauss-lemma bridge should consume `J = Psi.fst`, `K = Psi.snd`,
`HasDerivAt J (K t) t`, and the already local metric differentiability payload.

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicDependence
```

Actual result:

```text
Built Poincare.Global.GeodesicDependence (4.3s)
Build completed successfully (2831 jobs).
```

The final target build had no diagnostics from `Poincare/Global/GeodesicDependence.lean`;
the displayed warnings are existing replayed warnings from earlier modules.
