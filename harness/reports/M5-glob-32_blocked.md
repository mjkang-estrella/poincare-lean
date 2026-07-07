# M5-glob-32 blocked: augmented geodesic-data discharge landed

## Status

Blocked on the fully non-hypothetical `D`-field differentiability required by
`FTransition`, with verified strict-partial progress in the required new Lean
file:

- `Poincare/Global/SecondDischarge.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_augmentedFlow_hasDerivAt_of_geodesic_linearized_data
```

It packages the split geodesic and first-variation curves

```lean
τ ↦ (α p τ, Φ p ψ τ)
```

as a solution of the augmented system

```lean
(p, ψ)' = (geodesicFlowField Γ p, linearizedGeodesicFlowOperator Γ p ψ)
```

at `Γ = chartChristoffelField g x₀`, derives `C¹` regularity and compact
closed-ball Lipschitz control for `augmentedGeodesicFlowField Γ`, and then
instantiates `augmentedFlow_hasDerivAt_of_secondVariation_gronwall`.

The result is the fixed-time augmented derivative:

```lean
HasDerivAt
  (fun s =>
    (α (z + s • η).1 t,
      Φ (z + s • η).1 (z + s • η).2 t))
  (Ξ t) 0
```

assuming the second-variation curve `Ξ` solves the exported
`secondVariationFlowFieldAlong` equation on the same interval.

## Blocking boundary

This discharges the augmented ODE combination plus the compact Taylor/Lipschitz
field side at the geodesic chart-Christoffel data.  The repository still lacks
the final exported bridge from these augmented directional derivatives to the
chart-indexed Frechet differentiability package needed by `FTransition`:

```lean
HasFDerivAt D (fderiv ℝ D (eM v)) (eM v)
```

In particular, there is no current API turning the second-variation endpoint
family into a neighborhood-level derivative field for `fderiv ℝ F`, with the
required endpoint linearity/continuity and symmetry data, and no exported
conversion from that field to the selected Cartan `DF` field used by
`GermAndField`/`FTransition`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/SecondDischarge.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/SecondDischarge.lean
git diff --check -- Poincare/Global/SecondDischarge.lean
lake build Poincare.Global.SecondDischarge
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
43:theorem chartChristoffel_augmentedFlow_hasDerivAt_of_geodesic_linearized_data

git diff --check -- Poincare/Global/SecondDischarge.lean
exit status 0

lake build Poincare.Global.SecondDischarge
Built Poincare.Global.SecondDischarge
Build completed successfully (2838 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
