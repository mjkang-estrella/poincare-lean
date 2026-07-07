# M5-rigid-59 blocked: algebraic hosted equality chain verified, pinned hosted inputs still missing

## Status

Added `Poincare/Global/EqualityChain.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module proves the non-vacuous algebraic chain requested in this task:
if the source and target hosted endpoint pairings are pinned to matching
`sin^2` anchor-metric values, then `CartanMap.TangentAlignment.map_app`
identifies the anchor pairings and yields the verbatim hosted endpoint-pairing
feed consumed by `PairingFeed.lean`.

## Verified payload

The new module exports:

```lean
Poincare.EqualityChain.hostedTargetSpeed_eq_hostedSourceSpeed
Poincare.EqualityChain.hostedTargetTransverseScale_eq_hostedSourceTransverseScale
Poincare.EqualityChain.hosted_sin_sq_factor_eq
Poincare.EqualityChain.hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
Poincare.EqualityChain.hosted_endpoint_pairing_feed_of_common_sin_sq_anchor_pairings
Poincare.EqualityChain.cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pairings
```

The central feed theorem proves exactly:

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
      (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
    CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
      (Ψs a Ts).1 (Ψs a' Ts).1
```

from:

```lean
Real.sin θt ^ 2 = Real.sin θs ^ 2
```

plus the two pinned formulas:

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
      (Ψs a Ts).1 (Ψs a' Ts).1 =
    Real.sin θs ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a'
```

and

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
      (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
    Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')
```

It then feeds that equality into
`PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed`.

## Remaining blocker

No current exported theorem derives the two pinned hosted formulas above for
the actual `Ψs` and `Ψt` families produced by the cascade.

The available upstream theorem
`CartanIsometryPackage.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique`
is still stated for a single side with three separately supplied trajectories
`Ψw`, `Ψw'`, and `Ψadd`, and it requires the quadratic norm identities,
linearized uniqueness hypotheses, and interval membership data explicitly.
There is no exported family-level theorem that converts the cascade-produced
hosted data into the displayed all-`a a'` pinned endpoint formula at the
`expAtChartOpenPartialHomeomorph` endpoint.

The target side has the same gap after specializing to
`roundSphereMetric3_hasConstantSectionalCurvature_one`: the constant-curvature
witness is available, but the endpoint-pinned all-`a a'` pairing theorem for
the hosted target family is not exported.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/EqualityChain.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/EqualityChain.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.EqualityChain
```

Actual result: succeeded. The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3172/3172] Built Poincare.Global.EqualityChain (2.9s)
Build completed successfully (3172 jobs).
```
