# M4-pinch-11 partial progress / quadratic expansion bridge

## Completed proof-bearing work

Added the anchored four-index Gram expansion:

```lean
metricVariationRicciPairingAt_ricci_eq_sum_gram_inv
```

It proves, under `hG : IsUnit (gramMatrix g x y)`, that

```lean
metricVariationRicciPairingAt g (ricciVariationField g) y =
  sum a, sum b, sum c, sum d,
    (gramMatrix g x y)^-1 a c *
    (gramMatrix g x y)^-1 b d *
    g.ricciAt y (gramFrame x y a) (gramFrame x y b) *
    g.ricciAt y (gramFrame x y c) (gramFrame x y d)
```

The proof is non-vacuous:

- rewrites the pairing through `metricVariationRicciPairingAt_ricci`;
- adds `sum_basis_coord_inner_eq_inner`;
- adds `ricciNormSqAt_eq_basis_sum` for an arbitrary basis and raised dual
  coframe;
- specializes to `gramFrameBasis g x y hG`;
- expands both raised Ricci slots using
  `metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv` and the existing
  tensor slot linearity lemmas.

## Remaining blocker

The requested second theorem is still not completed:

```lean
extDerivFun
  (fun y : M =>
    metricVariationRicciPairingAt g (ricciVariationField g) y) x v =
  2 * covRicciRicciPairingAt g x v
```

After the anchored expansion, the remaining proof is exactly the four-factor
derivative/cancellation step from `M4-pinch-10_blocked.md`:

1. product-rule expand the two inverse-Gram entries and the two Ricci entries;
2. rewrite inverse-Gram derivatives with
   `gramMatrix_inv_extDerivFun_eq_neg_sum` and
   `spatialMetricDerivAt_eq_leviCivita`;
3. rewrite both Ricci-entry derivatives with
   `closedRicciDerivativeExpansionAt_canonical`;
4. prove the two inverse-Gram groups cancel the four Levi-Civita correction
   groups;
5. merge the two remaining covariant-Ricci groups with
   `covTensor2DerivAt_ricciVariationField_symm` and `g.ricciAt_symm`.

I stopped rather than introducing a packaged product-rule or cancellation
hypothesis, because that would be an assumption-shaped replacement for the
missing proof.

## Verification

`lake env lean Poincare/Global/ScalarVariation.lean` succeeded after the
anchored expansion changes.  The final requested
`lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`
succeeded with warnings only.
