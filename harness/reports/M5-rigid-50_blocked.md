# M5-rigid-50 blocked: hosted derivative calculus proved, acceleration bridge still missing

## Status

Blocked for the requested unconditional `hΦderHosted` discharge.  I added
the new module `Poincare/Global/HarmonicHosted.lean` and did not edit existing
Lean modules, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.HarmonicHosted.hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq
```

It proves the verbatim hosted `HasDerivWithinAt` shape for the time-rescaled
harmonic state

```lean
fun τ : ℝ => ((Φ w (speed * τ)).1, speed • (Φ w (speed * τ)).2)
```

from:

1. interval transport for `τ ↦ speed * τ`,
2. the harmonic first-order ODE for `Φ w`,
3. the single pointwise coordinate-acceleration identity

```lean
coordinateJacobiAcceleration
    (GeodesicTransport.chartChristoffelField g x₀) (γ t)
    ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) =
  (speed * speed) • (-(Φ w (speed * t)).1)
```

The proof uses `scomp_of_eq` for the within-interval time rescaling,
projects the harmonic derivative to first and second components, and then uses
`linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator` plus
`coordinateJacobiFlowOperator_apply` to turn the acceleration identity into
the hosted linearized vector field.

## Remaining blocker

The full task still needs the acceleration identity above from the geometric
ingredients.  I did not find an exported theorem converting

```lean
coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
```

plus the hosted `D = K + Gamma(z)(V,J)` bookkeeping into the coordinate
acceleration identity for the abstract rescaled harmonic state.  The available
`JacobiNormClose.chart_linearized_state_feeds_norm_system_at` bridge is
one-way for an already-known chart-linearized solution; it does not construct
the coordinate acceleration equation for `Φ` itself.

Assuming that acceleration identity inside `HarmonicHosted.lean` is the
smallest non-vacuous boundary I could isolate without restating
`hΦderHosted` directly.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/HarmonicHosted.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/HarmonicHosted.lean
```

Actual result:

```text
35:theorem hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/HarmonicHosted.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.HarmonicHosted
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully with no local warning.

Final build lines:

```text
✔ [3163/3163] Built Poincare.Global.HarmonicHosted (2.6s)
Build completed successfully (3163 jobs).
```
