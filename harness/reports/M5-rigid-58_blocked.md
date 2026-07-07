# M5-rigid-58 blocked: endpoint-pairing feed isolated, hosted derivation still missing

## Status

Added `Poincare/Global/PairingFeed.lean` and did not edit existing Lean modules,
including `Poincare.lean`.

The new module proves the non-vacuous consumer from one endpoint-pairing feed
to the `cartanMap_isLocalIsometry`-shaped conclusion.  It also proves the
hosted `Ψ.1` version using the CLM-to-state-pairing conversion from
`PairingRoute.lean`.

## Verified payload

The new module exports:

```lean
Poincare.PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_derivative_endpoint_pairing_equality
Poincare.PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed
```

The first theorem shows that the Cartan chain-rule derivative plus one
derivative endpoint-pairing equality suffices:

```lean
(hEndpointPairing :
  ∀ a a' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a'))
```

The hosted theorem then rewrites `A` and `B` through their
`linearizedEndpointCLM`s and reduces the whole task to the hosted endpoint
state-pairing feed:

```lean
(hEndpointPairingFeed :
  ∀ a a' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        (Ψs a Ts).1 (Ψs a' Ts).1)
```

This is the single remaining feed hypothesis after both hosted sides and the
endpoint CLM conversions are aligned.

## Remaining blocker

No current exported theorem derives `hEndpointPairingFeed` from the hosted
facts named in the task.

The available facts are still one layer upstream:

* `CartanIsometryPackage.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique`
  is stated for separate hosted trajectories with initial data `w`, `w'`, and
  `w + w'`, and its scalar is pinned to `chartGeodesicMetric` at
  `extChartAt I x₀ x₀`.
* The strict-derivative cascade hosts the endpoint CLM with initial data
  `T⁻¹ • a`, so the endpoint-pairing feed needs the missing normalization from
  that pinned scalar to the derivative input `a`.
* The source endpoint target in `PairingRoute` is the chart metric at
  `(GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v`; the
  Jacobi payloads are still hosted at `(u,T)` and require the exported
  `T`, `u`, and `v = T • u` endpoint conversion before they can fill the
  displayed feed.
* The target side needs the same conversion for `roundSphereMetric3`, using
  `roundSphereMetric3_hasConstantSectionalCurvature_one`; the conformal
  round-sphere chart-weight identities alone do not produce the strict
  derivative endpoint pairing for `Ψt`.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/PairingFeed.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/PairingFeed.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.PairingFeed
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3154/3154] Built Poincare.Global.PairingFeed (11s)
Build completed successfully (3154 jobs).
```

