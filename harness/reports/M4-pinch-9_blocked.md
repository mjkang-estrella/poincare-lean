# M4-pinch-9 partial completion / Ricci-norm Bochner blocker

## Verified commits

- `e90a838d` - added `roughRicciLaplacianPairingAt`, the closed scalar
  `⟨roughTensorLaplacianAt Ric, Ric⟩_g`, plus its unfolded basis-sum lemma.
- `2e2eb11e` - added the first-derivative target vocabulary
  `covRicciRicciPairingAt = ⟨∇_v Ric, Ric⟩_g`, plus the honest reduction
  `extDerivFun_ricciNormSqAt_eq_metricVariationRicciPairingAt_ricci`.

Both commits were checked with:

```bash
lake build Poincare.Global.ScalarVariation
```

## What is now available

The rough-Ricci pairing requested in plan item 1 is now a concrete closed
definition:

```lean
roughRicciLaplacianPairingAt g x
```

It unfolds to the metric trace pairing of
`roughTensorLaplacianAt g (ricciVariationField g)` with `ricciVariationField g`.

The expected first-derivative RHS for plan item 2 is named:

```lean
covRicciRicciPairingAt g x v
```

and the derivative of `ricciNormSqAt` is reduced to differentiating the existing
Ricci/Ricci metric pairing:

```lean
extDerivFun (fun y => g.ricciNormSqAt y) x v
  =
extDerivFun
  (fun y => metricVariationRicciPairingAt g (ricciVariationField g) y) x v
```

## Blocker

The missing theorem is the non-vacuous closed product rule for the quadratic
double-raised Ricci pairing:

```lean
extDerivFun
  (fun y => metricVariationRicciPairingAt g (ricciVariationField g) y) x v
  =
2 * covRicciRicciPairingAt g x v
```

The existing Gram route proves `TraceMetricVariationDerivAt` for linear metric
traces `traceMetricVariationAt g h`.  It does not yet prove the analogous
product rule for

```lean
metricVariationRicciPairingAt g (ricciVariationField g)
```

where both raised tensor slots and the hard-coded Ricci factor vary with the
base point.  Using the already-proved time-derivative theorem would not be
honest here: it works at a fixed tangent fiber and does not provide the spatial
moving-fiber raise/lower cancellation needed for `extDerivFun`.

I did not state the Bochner identity or parabolic inequality with this missing
product rule as a hypothesis, because that would be an assumption-packaged
replacement for the requested proof rather than proof-bearing progress.

## Next proof unit

1. Prove a closed spatial derivative theorem for
   `metricVariationRicciPairingAt g h` when `h = ricciVariationField g`.
   The direct target is:

   ```lean
   extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
   ```

2. Differentiate that theorem once more and trace over the derivative slot,
   using `covTensor2SecondDerivAt` and the existing Schwarz/trace tools, to prove:

   ```lean
   g.laplacianAt (fun y => g.ricciNormSqAt y) x
     =
       2 * roughRicciLaplacianPairingAt g x
         + 2 * covRicciNormSqAt g x
   ```

3. Only after that identity is proved, combine it with
   `covRicciNormSqAt_nonneg` and
   `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt(_reaction3)` to state
   the requested parabolic `|Ric|^2` inequality.
