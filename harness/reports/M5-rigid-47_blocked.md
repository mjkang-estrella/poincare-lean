# M5-rigid-47 blocked: final composition stops at hosted endpoint identification

## Status

Blocked for the requested unconditional `cartanMap_isLocalIsometry`-shaped
composition.  I added the new module
`Poincare/Global/CartanFinalComposition.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The new module proves the pointwise scale normalization needed to align the
fixed strict-derivative time `T` from the cascade with the hosted scale
consumer:

```lean
Poincare.CartanFinalComposition.hostedDeltaForTime
Poincare.CartanFinalComposition.workingTime_hostedDeltaForTime
Poincare.CartanFinalComposition.workingVelocity_hostedDeltaForTime
Poincare.CartanFinalComposition.hostedSourceTransverseScale_hostedDeltaForTime
Poincare.CartanFinalComposition.hostedTargetTransverseScale_hostedDeltaForTime
```

For nonzero `v` and nonzero `T`, choosing
`hostedDeltaForTime T v = 2 * ‖v‖ / T` makes
`CartanHomogeneity.workingTime` equal `T` and
`CartanHomogeneity.workingVelocity` equal `T⁻¹ • v`.  This closes the scale
bookkeeping needed to use `CartanScaleGeneric` pointwise after the common
shrunk source/target strict-derivative cascade.

## Remaining blocker

The first action-equation hypothesis I cannot feed from the current exported
API is the endpoint identification inside

```lean
Poincare.CartanActionEquations.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
```

Verbatim missing hypothesis:

```lean
(hendpoint :
  (Ψ (CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
    (Φ (CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * T)).1)
```

`CartanCascade` produces the hosted linearized family `Ψ` and the strict
derivative CLM, and `CartanActionEquations` can consume a rescaled harmonic
solution `Φ` once this equality is supplied.  I did not find an exported theorem
that identifies the cascade-produced linearized endpoint with the rescaled
harmonic endpoint at `speed * T` for each transverse component.

Assuming this equality in the final file would be exactly restating the missing
bridge needed to construct the source/target action equations, so I stopped at
the verified scale-normalization boundary.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanFinalComposition.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanFinalComposition.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanFinalComposition
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3169/3169] Built Poincare.Global.CartanFinalComposition (13s)
Build completed successfully (3169 jobs).
```
