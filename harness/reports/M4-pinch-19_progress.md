# M4-pinch-19 progress: completed-square expansion isolated

## Formalized

- Added `ClosedSmoothRiemannianMetric.pinchingMixedGradientPairingAt`, the
  orthogonal-frame contraction for `⟨∇Ric, ∇R ⊗ Ric⟩`.
- Added `ClosedSmoothRiemannianMetric.pinchingScalarRicciGradientProductAt`, the
  matching raw norm contraction for `∇R ⊗ Ric`.
- Proved
  `ClosedSmoothRiemannianMetric.pinchingGradientSquareAt_eq_completedSquareExpansion`:

```text
|R ∇Ric - ∇R ⊗ Ric|²
  = R² |∇Ric|² - 2 R ⟨∇Ric, ∇R ⊗ Ric⟩
      + |∇R ⊗ Ric|²_raw
```

- Proved `pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions`:
  the named obligation `PinchingQuotientCompletedSquareIdentityAt` follows from
  the explicit quotient/drift spatial expansion

```text
ΔQ + drift
  = ΔN/R² - 2 N ΔR/R³
      - 4 cross/R³ + 2 rawProduct/R⁴.
```

- Added
  `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion`,
  which replaces the opaque completed-square hypothesis in the quotient
  evolution assembly with that explicit spatial expansion.

## Remaining boundary

This is verified progress but not the full task discharge.  The remaining step
is to prove the spatial expansion itself from the existing quotient
product-rule lemmas, including the Gram bridges:

- `cross = covRicciRicciPairingAt g x (g.gradientAt scalar x)`;
- `rawProduct = scalarGradNormSqAt g x * ricciNormSqAt g x`;
- the quotient-rule expansions for `ΔQ` and `(2/R)⟨∇R,∇Q⟩` under the honest
  nonzero-scalar/product-rule domain assumptions.

## Verification

- `lake env lean Poincare/Global/ScalarEvolution.lean`
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ScalarEvolution.lean`
  returned no matches.
- `git diff --check`
