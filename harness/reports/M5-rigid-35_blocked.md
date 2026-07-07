# M5-rigid-35 blocked: hosted Cartan discharge

## Status

Blocked.  I did not add `Poincare/Global/CartanHostedDischarge.lean`, because
the requested theorem would have to invent or re-assume the two hypothesis
families it is supposed to discharge.

## Target theorem audited

The hosted bridge

```lean
Poincare.CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings
```

still requires the two remaining hypothesis families explicitly:

- strict source and target endpoint derivatives
  `hsourceDeriv` / `htargetDeriv`
- differential-action equations `hDu` / `hDu'`

Those are the exact assumptions at
`Poincare/Global/CartanScaleGeneric.lean:86-103`.

## Blocking evidence

1. **General strict derivatives are not exported.**

   The only exported strict derivative of the exponential chart is the anchored
   theorem

   ```lean
   GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
   ```

   in `Poincare/Global/ExponentialLocalHomeo.lean:231-236`.  The partial
   homeomorphism is then built from that zero derivative at
   `Poincare/Global/ExponentialLocalHomeo.lean:416-424`.

   I searched the exponential/geodesic/Cartan modules for
   `HasStrictFDerivAt`, `HasFDerivAt`, `fderiv`, and
   `expAtChartOpenPartialHomeomorph`.  I found no theorem proving

   ```lean
   HasStrictFDerivAt
     (GeodesicTransport.expAtChartOpenPartialHomeomorph ...)
     A v
   ```

   for arbitrary nonzero `v` in the shrunk source.  The hosting theorem
   `CartanHomogeneity.exists_shrunk_cutoff_one_homogeneity_conversion`
   exports a shrunk source ball and a radial one-dimensional derivative
   at `(u,T)` (`CartanHomogeneity.lean:115-157`), but not a strict Frechet
   derivative or continuous-linear-equivalence candidate at the endpoint.

2. **The hosted differential action is not exported.**

   `CartanDifferential.lean` has directional endpoint derivative ingredients:
   radial (`CartanDifferential.lean:59-123`) and transverse
   (`CartanDifferential.lean:133-300`).  It also has the strict chain rule
   consumer `cartanChartMap_hasStrictFDerivAt_of_expAtChart`
   (`CartanDifferential.lean:328-379`), but that consumer assumes both strict
   exponential derivatives.

   There is no exported theorem identifying

   ```lean
   CartanLocalIsometry.cartanChartDifferential L A B u
   ```

   with

   ```lean
   CartanLocalIsometry.targetScaledNormalVector L
     (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u
   ```

   for the hosted `(u,T)` endpoint differential.  The Cartan isometry
   theorem/package files supply scalar and pairing identities, not this
   Frechet-level action equation.

3. **Instantiating the final local-isometry theorem would be vacuous.**

   Any new theorem in `CartanHostedDischarge.lean` that calls the hosted bridge
   today must still take `hsourceDeriv`, `htargetDeriv`, `hDu`, and `hDu'` as
   assumptions, or must assume an equivalent bundled endpoint differential
   surface.  That would not discharge the two requested families and would
   violate the worker contract's no-vacuous-wrapper rule.

## Required build

Command:

```bash
lake build Poincare.Global.CartanHostedDischarge
```

Actual result: failed, because no non-vacuous `CartanHostedDischarge.lean`
module was added.

Final output:

```text
error: no such file or directory (error code: 4294967294)
  file: /Users/mjkang/Develop/poincare-wt-M5-rigid-35/Poincare/Global/CartanHostedDischarge.lean
Some required targets logged failures:
- Poincare.Global.CartanHostedDischarge
error: build failed
```

## Next proof surface needed

A non-vacuous discharge needs a new endpoint-differential theorem, upstream of
`CartanScaleGeneric`, proving on a positive shrunk ball that the fixed-time
exponential chart has a strict Frechet derivative at every nonzero hosted
endpoint and that this derivative acts on the radial/transverse decomposition
with the hosted radial and transverse scales.  The target statement then needs
the same theorem for `roundSphereMetric3`, followed by the tangent-alignment
intertwining.
