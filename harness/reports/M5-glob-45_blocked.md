# M5-glob-45 blocked: augmented compact-tube remainders exported

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/AugmentedPackage.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_augmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
```

For the chart-Christoffel augmented geodesic/first-variation field

```lean
augmentedGeodesicFlowField (chartChristoffelField g x₀)
```

on any compact convex augmented tube `Kset`, the theorem exports the uniform
Taylor remainder

```lean
‖F q - F base -
    secondVariationFlowOperator (chartChristoffelField g x₀) base (q - base)‖
  ≤ ε * ‖q - base‖
```

whenever `base, q ∈ Kset` and `‖q - base‖ ≤ δ`.

The proof uses the field-generic compact-uniform Taylor theorem from
`GeodesicDerivative.lean` and obtains `ContDiff ℝ 1` for the concrete augmented
field from `AugmentedC1.lean`.  The derivative term is unfolded to the existing
`secondVariationFlowOperator`.

## Blocking boundary

This closes the stage-(3) uniform-remainder export for the augmented field, but
does not yet construct the neighborhood derivative-field package required by
`ExpChartC2.lean`:

```lean
sourceD targetD : E3 → E3 →L[ℝ] E3
∀ q ∈ U, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
∀ q ∈ U, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

The remaining work is to identify the second-variation endpoint operators with
the exponential-chart derivative fields on a neighborhood and prove their
`C¹` dependence, then feed that package through `ExpChartC2`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/AugmentedPackage.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/AugmentedPackage.lean
git diff --check -- Poincare/Global/AugmentedPackage.lean
lake build Poincare.Global.AugmentedPackage
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
37:theorem chartChristoffel_augmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex

git diff --check -- Poincare/Global/AugmentedPackage.lean
exit status 0

lake build Poincare.Global.AugmentedPackage
✔ [2836/2836] Built Poincare.Global.AugmentedPackage (13s)
Build completed successfully (2836 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
