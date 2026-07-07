# M5-rigid-63 done: source rescaled feed and scalar normalizations

## Status

Added `Poincare/Global/SourcePackage.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module mirrors `TargetPackage.lean` on the source metric by replacing
the round-sphere witness with an explicit
`HasConstantSectionalCurvature3 g 1` hypothesis.  It also proves the scalar
normalizations needed to remove the explicit scale assumptions in
`UnscaledFeed.lean` for common nonzero hosted time.

## Verified payload

Source rescaled feed:

```lean
Poincare.SourcePackage.source_normA_eq_pinned_on_cutoff_one_Icc
Poincare.SourcePackage.source_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
Poincare.SourcePackage.source_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package
```

Scalar normalizations and hosted bookkeeping:

```lean
Poincare.SourcePackage.normalizedRescaledAngle
Poincare.SourcePackage.abs_sin_mul_inv_le_one
Poincare.SourcePackage.sin_normalizedRescaledAngle
Poincare.SourcePackage.rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
Poincare.SourcePackage.hostedTransverseScaleFromSpeed_sq_eq_rescaled_sin_sq
Poincare.SourcePackage.norm_workingVelocity_eq_half
Poincare.SourcePackage.hostedDeltaForTime_rescaled_sin_sq_factor
Poincare.SourcePackage.hosted_source_target_normalized_sin_sq_eq
```

Feed-through consumers:

```lean
Poincare.SourcePackage.hosted_endpoint_pairing_feed_of_common_rescaled_anchor_pairings
Poincare.SourcePackage.cartanMap_isLocalIsometry_on_normalBall_of_common_rescaled_anchor_pairings
```

The last theorem invokes the wired `UnscaledFeed` local-isometry consumer with
the source and target rescaled endpoint feeds at a common nonzero hosted time,
discharging:

```lean
Real.sin T ^ 2 * (T⁻¹ * T⁻¹) =
  Real.sin (normalizedRescaledAngle T) ^ 2
```

on both sides and using `rfl` for the resulting common `hSin`.

## Verification

Reserved-token scan over `Poincare/Global/SourcePackage.lean`:

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/SourcePackage.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.SourcePackage
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings.
The new module also has three nonfatal unused-section-variable linter warnings
where `[T2Space M]` remains in scope for scalar/feed theorems that only need the
weaker `UnscaledFeed` assumptions.

Final build lines:

```text
⚠ [3177/3177] Built Poincare.Global.SourcePackage (3.2s)
Build completed successfully (3177 jobs).
```
