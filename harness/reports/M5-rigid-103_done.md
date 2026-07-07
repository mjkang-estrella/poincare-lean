# M5-rigid-103 done: scaled positive factor upgrades endpoint CLMs

## Outcome

Added `Poincare/Global/ScaledUpgrade.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves the scaled positive-definite upgrade requested after
the M5-rigid-102 scalar pin:

```lean
Poincare.ScaledUpgrade.injective_of_scaled_pullback_posDef
Poincare.ScaledUpgrade.exists_continuousLinearEquiv_of_scaled_pullback_posDef
```

These thread one positive scalar through the same kernel argument used by
`PairingUpgrade`: if

```lean
G (D u) (D u') = c * S u u'
```

with `0 < c` and `S` positive definite, then `D u = 0` forces
`c * S u u = 0`, hence `S u u = 0`, hence `u = 0`.  Finite-dimensional
endomorphism injectivity then gives the continuous linear equivalence.

## Hosted endpoint constructors

The module adds source and target anchor specializations, then hosted endpoint
CLM versions:

```lean
Poincare.ScaledUpgrade.exists_continuousLinearEquiv_of_scaled_sourceAnchor_pullback
Poincare.ScaledUpgrade.exists_continuousLinearEquiv_of_scaled_targetAnchor_pullback
Poincare.ScaledUpgrade.exists_continuousLinearEquiv_of_scaled_source_linearizedEndpointCLM_pullback
Poincare.ScaledUpgrade.exists_continuousLinearEquiv_of_scaled_target_linearizedEndpointCLM_pullback
```

The final consumer does accept the common scaled form.  The combined adapter

```lean
Poincare.ScaledUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_scaled_hosted_anchor_pullbacks
```

constructs the endpoint equivalences `A` and `B`, preserves the exact coercion
equalities to the selected `linearizedEndpointCLM`s, and feeds
`PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed`.
The common scalar cancels between source and target through
`CartanMap.TangentAlignment.map_app`.

For the shrunk sine-square case, the module also records

```lean
Poincare.ScaledUpgrade.sin_sq_pos_of_mem_Ioo
Poincare.ScaledUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pullbacks
```

where `Real.sin θ ^ 2` is positive from `θ ∈ Set.Ioo 0 Real.pi`.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/ScaledUpgrade.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/ScaledUpgrade.lean`
  - Result: success.
- `lake build Poincare.Global.ScaledUpgrade`
  - Result: success.
  - Final lines:

```text
✔ [3156/3156] Built Poincare.Global.ScaledUpgrade (13s)
Build completed successfully (3156 jobs).
```
