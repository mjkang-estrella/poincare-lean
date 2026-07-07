# M5-rigid-34 done: scale-generic Cartan bridge

## Files

- Edited `Poincare/Global/CartanCoefficientBridge.lean`.
- Added `Poincare/Global/CartanScaleGeneric.lean`.
- Added this report.

## Verified progress

`CartanCoefficientBridge.lean` now has an additive scale-generic bridge:

```lean
Poincare.CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_scale_generic_endpoint_pairings
```

It keeps the existing hardcoded `transverseScale` theorem unchanged.  The new
theorem parameterizes the bridge over radial and transverse scale functions
`rho sigma : E -> R`, uses source radial/radial, radial/transverse, and
transverse/transverse endpoint blocks with those scales, and combines them with
a target metric block plus weighted anchor comparison at the same scales.

`CartanScaleGeneric.lean` defines the hosted scale data:

```lean
hostedRadialScale
hostedSourceSpeed
hostedTargetSpeed
hostedTransverseScaleFromSpeed
hostedSourceTransverseScale
hostedTargetTransverseScale
```

The hosted transverse factor is the honest working-speed/time expression

```lean
sin (speed * workingTime delta v) / (speed * workingTime delta v)
```

with `speed` measured from `CartanHomogeneity.workingVelocity delta v`.

The new module contains one isolated hosted bridge theorem:

```lean
Poincare.CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings
```

It accepts source endpoint blocks using the source hosted scale and target
endpoint data using the target hosted scale.  In the proof, the target scale is
rewritten to the source scale by `CartanMap.TangentAlignment.map_app`, then the
scale-generic coefficient bridge supplies the local-isometry conclusion.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/CartanCoefficientBridge.lean \
  Poincare/Global/CartanScaleGeneric.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- \
  Poincare/Global/CartanCoefficientBridge.lean \
  Poincare/Global/CartanScaleGeneric.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanCoefficientBridge Poincare.Global.CartanScaleGeneric
```

Actual result: success, with pre-existing upstream warnings replayed.  Final
line:

```text
Build completed successfully (3158 jobs).
```
