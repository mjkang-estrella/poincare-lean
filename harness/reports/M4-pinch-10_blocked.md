# M4-pinch-10 blocked / quadratic Ricci-norm derivative

## Target

The requested frozen theorem is:

```lean
extDerivFun
  (fun y : M =>
    metricVariationRicciPairingAt g (ricciVariationField g) y) x v =
  2 * covRicciRicciPairingAt g x v
```

Equivalently, using the already proved pointwise identity
`metricVariationRicciPairingAt_ricci`, this is the first spatial derivative of
`g.ricciNormSqAt`:

```lean
extDerivFun (fun y : M => g.ricciNormSqAt y) x v =
  2 * covRicciRicciPairingAt g x v
```

## What I verified before stopping

The worktree initially had a stale `.olean`: importing
`Poincare.Global.ScalarVariation` did not expose the pinch-9 names
`covRicciRicciPairingAt` or
`extDerivFun_ricciNormSqAt_eq_metricVariationRicciPairingAt_ricci`.  A fresh
build of `Poincare.Global.ScalarVariation` succeeded and refreshed the cache.

After that build, Lean sees both names, and the target reduces exactly to the
missing `|Ric|^2` first-derivative theorem:

```lean
rw [<- extDerivFun_ricciNormSqAt_eq_metricVariationRicciPairingAt_ricci
  (g := g) (x := x) (w := v)]
```

leaves:

```lean
extDerivFun (fun y : M => g.ricciNormSqAt y) x v =
  2 * covRicciRicciPairingAt g x v
```

## Available proof-bearing ingredients

The linear trace route is fully available:

- `traceMetricVariationAt_eq_sum_gram_inv`
- `traceMetricVariationAt_extDerivFun_eq_gram_rhs`
- `gram_rhs_extDerivFun_eq_sum_product`
- `gramMatrix_inv_extDerivFun_eq_neg_sum`
- `gram_inv_deriv_contraction_eq_leviCivita_corrections`
- `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt`

The Ricci derivative vocabulary is also available:

- `covTensor2DerivAt`
- `covTensor2DerivAt_ricciVariationField_symm`
- `closedRicciDerivativeExpansionAt_canonical`
- `covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt`
- `covTensor2ExtDifferentiableAt_ricciVariationField_canonical`
- `covRicciRicciPairingAt`

## Blocker

There is still no non-vacuous quadratic analogue of the linear trace product
rule.  The needed proof is not just a rewrite through
`metricVariationRicciPairingAt_ricci`: it must differentiate the double-raised
Ricci contraction, where four factor groups vary:

1. the first Gram-inverse / raised slot,
2. the second Gram-inverse / raised slot,
3. the first Ricci entry,
4. the second Ricci entry.

The current linear theorem cancels one Gram-inverse derivative against the two
Levi-Civita corrections for a single `(0,2)` tensor trace.  The requested
theorem needs the quadratic version: two Gram-inverse derivative blocks plus
two Ricci-entry derivative blocks, with the two Ricci-entry contributions
recognized as identical by Ricci and covariant-Ricci symmetry.

I did not add a theorem with a new hypothesis such as a packaged
`RicciNormSqFirstDerivativeAt`, because that would be an assumption-shaped
replacement for the missing proof.

## Next proof unit

Prove a closed anchored expansion for the Ricci/Ricci pairing:

```lean
metricVariationRicciPairingAt g (ricciVariationField g) y =
  sum a, sum b, sum c, sum d,
    (gramMatrix g x y)^-1 a c *
    (gramMatrix g x y)^-1 b d *
    g.ricciAt y (gramFrame x y a) (gramFrame x y b) *
    g.ricciAt y (gramFrame x y c) (gramFrame x y d)
```

near `x`, under `gramMatrix_eventually_isUnit`.

Then prove the four-factor product-rule derivative at `x`:

- use `gramMatrix_inv_extDerivFun_eq_neg_sum` and
  `spatialMetricDerivAt_eq_leviCivita` for both inverse-Gram factors;
- use `closedRicciDerivativeExpansionAt_canonical` for both Ricci-entry
  derivative factors;
- cancel the four Levi-Civita correction groups against the two inverse-Gram
  derivative groups;
- use `covTensor2DerivAt_ricciVariationField_symm` and `g.ricciAt_symm` to
  combine the two remaining Ricci-entry terms into
  `2 * covRicciRicciPairingAt g x v`.

This is the precise missing bridge before the pinch-9 plan can continue to the
second derivative / Bochner identity.
