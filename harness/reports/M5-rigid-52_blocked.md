# M5-rigid-52 blocked: hosted derivative assembled to source action, correction collapse remains

## Status

Blocked for the requested unconditional local-isometry theorem.  I added the
new module `Poincare/Global/CartanTheIsometry.lean` and did not edit existing
Lean modules, including `Poincare.lean`.

## Verified payload

The new module exports two non-vacuous composition theorems:

```lean
Poincare.CartanTheIsometry.hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_identity
Poincare.CartanTheIsometry.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_acceleration_identity
```

The first theorem feeds

```lean
Poincare.AccelerationIdentity.coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state
```

into

```lean
Poincare.HarmonicHosted.hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq
```

so the old direct `hΦderHosted` hypothesis is no longer assumed.  The second
theorem feeds that assembled hosted derivative into

```lean
Poincare.CartanIsometryDone.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique
```

and therefore reaches the source-side action equation:

```lean
linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u =
  CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ
    (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u
```

## Remaining blocker

The M5-rigid-51 acceleration theorem intentionally preserves the Christoffel
correction terms.  `HarmonicHosted`, however, consumes the raw acceleration
shape

```lean
coordinateJacobiAcceleration
    (GeodesicTransport.chartChristoffelField g x₀) (γ t)
    ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) =
  (speed * speed) • (-(Φ w (speed * t)).1)
```

The exact remaining hypothesis isolated in the new module is the algebraic
collapse of the correction-bearing right-hand side:

```lean
(haccCollapse : ∀ t ∈ Icc (-ε) ε,
  -(Φ w (speed * t)).1 -
      (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) (γ t).1)
        (γ t).2) (γ t).2) (Φ w (speed * t)).1 +
    (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
      ((GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2)
      (Φ w (speed * t)).1 -
    (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
      (speed • (Φ w (speed * t)).2) -
    (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
      ((speed • (Φ w (speed * t)).2) +
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
          (γ t).2 (Φ w (speed * t)).1) =
    (speed * speed) • (-(Φ w (speed * t)).1))
```

Without this collapse, the coordinate acceleration identity cannot be converted
to the `HarmonicHosted` input.  Assuming the final local-isometry theorem past
this point would hide this real algebraic gap, so I stopped at the verified
source-action assembly.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanTheIsometry.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanTheIsometry.lean
```

Actual result:

```text
40:theorem hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_identity
109:theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_acceleration_identity
```

Direct Lean check:

```bash
lake env lean Poincare/Global/CartanTheIsometry.lean
```

Actual result: succeeded with no output.

Required build:

```bash
lake build Poincare.Global.CartanTheIsometry
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3165/3165] Built Poincare.Global.CartanTheIsometry (2.7s)
Build completed successfully (3165 jobs).
```
