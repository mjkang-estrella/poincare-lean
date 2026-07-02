# M3-predicates-22 done report

## Verified progress

This worker closed the contraction-side first-slot derivative bridge in
`Poincare/Global/ScalarVariation.lean`.

New δΓ-entry bridge vocabulary:

- `DeltaGammaEntryDerivativeBridgeAt`
- `deltaGammaEntryDerivativeBridgeAt_const`

The bridge is the scalar-entry formula

```lean
extDerivFun
  (fun y : M =>
    (gt t₀).inner y
      (deltaGammaAt gt t₀ y (extend E p y) (extend E w y))
      (extend E q y)) x u
=
  (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u p w) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E p) x u) w) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x p ((gt t₀).leviCivita (extend E w) x u)) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x p w)
      ((gt t₀).leviCivita (extend E q) x u)
```

The static witness is non-vacuous: for a constant metric family,
`deltaGammaAt` and `covDeltaGammaDerivAt` reduce to zero, and the scalar entry
is the zero function.

New proven bridge/cascade lemmas:

- `deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge`
- `deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_trace_extSecond`
- `deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt`

The proof routes the fixed-`w` scalar tensor
`hδ_y(p,q) = g(δΓ_y(p, extend w), q)` through the existing Gram/product-rule
engine `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt`.  The
new entry bridge identifies the covariant derivative of `hδ` as
`covDeltaGammaDerivAt` plus the extension-slot correction, which gives exactly
`DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt`.  The existing Hessian
adapter then discharges `DeltaGammaContractionTraceHessianDerivativeAt`.

## Verification

Focused check:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with pre-existing linter warnings.

Exact requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, with pre-existing linter warnings.
