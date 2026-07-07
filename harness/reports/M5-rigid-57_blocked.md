# M5-rigid-57 blocked: direct derivative-pairing bridge proved, endpoint feed still missing

## Status

Added `Poincare/Global/PairingRoute.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module proves the direct pairing route up to the exact derivative
endpoint-pairing feed.  It avoids the failed vector-level sine/action route:
the final Cartan pullback is now stated in terms of source and target endpoint
pairings of the exponential-chart strict derivatives.

## Verified payload

The new module exports four theorems:

```lean
Poincare.PairingRoute.derivative_pairing_eq_scaled_pairing_of_radial_transverse_blocks
Poincare.PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
Poincare.PairingRoute.cartanMap_isLocalIsometry_on_normalBall_of_weighted_derivative_endpoint_pairings
Poincare.PairingRoute.cartanMap_isLocalIsometry_on_normalBall_of_derivative_endpoint_pairings
```

The core bridge is `cartanMap_isLocalIsometry_on_normalBall_of_weighted_derivative_endpoint_pairings`.
It writes arbitrary endpoint chart vectors as `A.symm u` and `A.symm u'`,
uses the source derivative endpoint pairing on `A (A.symm u)`, uses the target
derivative endpoint pairing on `B (L (A.symm u))`, and then applies the weighted
anchor comparison to get the Cartan pullback identity.

The CLM bridge
`linearizedEndpointCLM_pairing_eq_state_endpoint_pairing` proves the exact
conversion needed by the hosted Jacobi facts:

```lean
G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul w)
  (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul w')
= G (Ψ w T).1 (Ψ w' T).1
```

The three-block algebra theorem packages radial-radial, radial-transverse, and
transverse-transverse endpoint pairings into one full derivative endpoint
pairing, without assuming a vector action equation for the derivative map.

## Remaining feed

The public API still does not expose the derivative endpoint pairings needed
to instantiate the final bridge from the existing hosted facts.  In the
same-weight specialization, the remaining feed is exactly:

```lean
(hSourcePairing :
  ∀ a a' : E,
    CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') =
      κ * CartanMap.sourceAnchorChartMetric g x₀ a a')

(hTargetPairing :
  ∀ a a' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
      κ * CartanMap.targetAnchorChartMetric p₀ (L a) (L a'))
```

The first new CLM theorem shows how to turn these into pairings of hosted
`Ψ.1` values once `A` and `B` are identified with the strict-derivative CLMs.
What is still missing is the exported endpoint conversion that instantiates
those two formulas from the existing hosted `(u,T)` Jacobi pairing theorems,
including the source/target hosted parameter alignment and the final packaged
continuous-linear equivalences used by the Cartan chain rule.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/PairingRoute.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/PairingRoute.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.PairingRoute
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3153/3153] Built Poincare.Global.PairingRoute (13s)
Build completed successfully (3153 jobs).
```
