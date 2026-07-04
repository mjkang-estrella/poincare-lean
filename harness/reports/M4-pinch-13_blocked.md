# M4-pinch-13 partial progress / Bochner product-rule blocker

## Verified progress

Added three proof-bearing lemmas in `Poincare/Global/ScalarVariation.lean`:

- `extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt`
- `hessianAt_ricciNormSqAt_eq_two_extDerivFun_covRicciRicciPairingAt_sub`
- `laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub`

The first lemma packages the existing Ricci/Ricci pairing derivative as the
direct spatial derivative of `ricciNormSqAt`.

The second lemma differentiates that first derivative through the closed
Hessian compatibility theorem:

```lean
g.hessianAt (fun y : M => g.ricciNormSqAt y) x u w =
  2 * extDerivFun
      (fun y : M => covRicciRicciPairingAt g y (extend E w y)) x u
    - 2 * covRicciRicciPairingAt g x
      (g.leviCivita (extend E w) x u)
```

The third lemma traces that Hessian bridge on the `laplacianAt` diagonal.  This
pins the exact diagonal pattern that the Bochner identity must expand.

Checked with:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

which completed with warnings only.

## Remaining blocker

The task's requested Bochner identity still needs the non-vacuous product-rule
expansion

```lean
extDerivFun
  (fun y : M => covRicciRicciPairingAt g y (extend E w y)) x u
```

into:

1. the second-covariant Ricci term paired with Ricci, and
2. the covariant-Ricci derivative paired with covariant-Ricci.

The current file has the first-order four-factor Gram chain for
`metricVariationRicciPairingAt g (ricciVariationField g)`, but it does not yet
have the analogous moving-frame product rule for `covRicciRicciPairingAt`.
That missing expansion is exactly what is needed before the trace can be
recognized as

```lean
2 * roughRicciLaplacianPairingAt g x + 2 * covRicciNormSqAt g x
```

and before the rough-pairing cancellation can be used to state the parabolic
`|Ric|^2` inequality honestly.

I did not add a Bochner theorem or parabolic inequality with a packaged
assumption for this missing expansion, because that would be an
assumption-shaped replacement for the requested proof.
