# M5-glob-30 done: second-variation augmented-system opener

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/SecondVariation.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module defines:

- `Poincare.augmentedGeodesicFlowField`: the augmented ODE
  `(p, ψ) ↦ (geodesicFlowField Γ p, linearizedGeodesicFlowOperator Γ p ψ)`.
- `Poincare.secondVariationFlowOperator`: the Fréchet linearization of the
  augmented vector field, i.e. the second-variation coefficient.
- `Poincare.secondVariationFlowFieldAlong`: the time-dependent linear
  second-variation ODE along an augmented curve.

It adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .exists_isPicardLindelof_chartChristoffel_secondVariation_linearODE
```

The theorem consumes a closed smooth Riemannian metric, an anchor point, and a
continuous augmented base curve `ζ`.  Internally it derives `C²` regularity of
the chart-Christoffel geodesic flow from the smooth blended metric, proves that
the augmented vector field is `C¹`, and reuses the existing generic continuous
linear-ODE PL package to produce local bounded-coefficient Picard-Lindelöf
data for `secondVariationFlowFieldAlong (chartChristoffelField g x₀) ζ`.

This is the requested augmented-system opener.  It does not claim the later
second-variation existence/uniqueness or the fixed-time differentiability
interface for `w ↦ Ψ_w(T)`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/SecondVariation.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/SecondVariation.lean
git diff --check -- Poincare/Global/SecondVariation.lean
lake build Poincare.Global.SecondVariation
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
27:def augmentedGeodesicFlowField
40:def secondVariationFlowOperator
47:def secondVariationFlowFieldAlong
76:theorem exists_isPicardLindelof_chartChristoffel_secondVariation_linearODE

git diff --check -- Poincare/Global/SecondVariation.lean
exit status 0

lake build Poincare.Global.SecondVariation
Built Poincare.Global.SecondVariation
Build completed successfully (2833 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully and introduced no reported warning.
