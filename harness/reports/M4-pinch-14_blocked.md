# M4-pinch-14 partial progress / cancellation blocker

## Verified progress

The moving-frame `covRicciRicciPairingAt` product-rule route now has proof-bearing
infrastructure in `Poincare/Global/ScalarVariation.lean`.

Added and checked:

- `covRicciRicciPairingAt_eq_metricVariationRicciPairingAt_movingCovTensor2DerivAt`
- `covRicciRicciPairingAt_eq_metricVariationRicciPairingAt_covTensor2DerivAt`
- `metricRicciPairingTraceInBasisAt` and its trace bridge
- `metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt`
- `metricVariationRicciPairingAt_eq_sum_gram_inv_of_symm`
- `covRicciDerivativeBilinFormAt`
- `metricVariationRicciPairingAt_covTensor2DerivAt_eq_sum_gram_inv`
- `covRicciPairingGramRHS` and the four product-rule groups
- `covRicci_pairing_gram_product_rule_expand`
- `extDerivFun_covRicciRicciPairingAt_extend_eq_covRicciPairingGramProductRuleRHS`
- `covRicciPairingCovRicciDerivGroup_eq_secondDerivExpansionGroup`
- `covRicciPairingSecondDerivExpansionGroup_eq_secondCovariant_plus_leviCorrections`
- `covRicciPairingDirectionLeviCorrectionGroup_eq_covRicciRicciPairingAt`

The literal blocked expression now reduces to product-rule groups:

```lean
extDerivFun
  (fun y : M => covRicciRicciPairingAt g y (extend E w y)) x u
  =
covRicciPairingGramProductRuleRHS g x u w
```

The `∂(∇Ric)` product group is also split into:

```lean
covRicciPairingSecondCovariantGroup g x u w
  + covRicciPairingDirectionLeviCorrectionGroup g x u w
  + covRicciPairingFirstSlotLeviCorrectionGroup g x u w
  + covRicciPairingSecondSlotLeviCorrectionGroup g x u w
```

and the direction correction is identified as:

```lean
covRicciRicciPairingAt g x
  (g.leviCivita (extend E w) x u)
```

This is the term that cancels against the subtraction already present in
`hessianAt_ricciNormSqAt_eq_two_extDerivFun_covRicciRicciPairingAt_sub` and
`laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub`.

Checked after each committed unit with:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

which completed with warnings only.

## Remaining blocker

The nontrivial cancellation/recognition layer remains:

1. Rewrite `covRicciPairingRicciDerivGroup` into the covariant-Ricci paired with
   covariant-Ricci plus the two Ricci-entry Levi-Civita corrections.
2. Prove the two inverse-Gram derivative groups cancel with the lower-slot
   Levi-Civita corrections from both differentiated tensor entries, following
   the pinch-12 `pairing_gram_inv_deriv_groups_cancel_...` template.
3. Identify the surviving second-covariant group on the Laplacian diagonal with
   `roughRicciLaplacianPairingAt g x`.
4. Identify the surviving covariant-Ricci/covariant-Ricci diagonal with
   `covRicciNormSqAt g x`.
5. Substitute into
   `laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub`
   and finish the traced Bochner identity, then combine it with
   `covRicciNormSqAt_nonneg` and
   `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt_reaction3` for the
   parabolic `|Ric|^2` inequality.

## Literal next goal

The next proof-bearing step should introduce the Ricci-entry derivative group:

```lean
noncomputable def covRicciPairingRicciCovariantGroup ...
noncomputable def covRicciPairingRicciFirstSlotLeviCorrectionGroup ...
noncomputable def covRicciPairingRicciSecondSlotLeviCorrectionGroup ...

theorem covRicciPairingRicciDerivGroup_eq_covariant_plus_leviCorrections
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    covRicciPairingRicciDerivGroup g x u w =
      covRicciPairingRicciCovariantGroup g x u w
        + covRicciPairingRicciFirstSlotLeviCorrectionGroup g x u w
        + covRicciPairingRicciSecondSlotLeviCorrectionGroup g x u w := by
  ...
```

Then prove the cancellation statement:

```lean
covRicciPairingGramInvFirstDerivGroup g x u w
  + covRicciPairingGramInvSecondDerivGroup g x u w
  + covRicciPairingFirstSlotLeviCorrectionGroup g x u w
  + covRicciPairingSecondSlotLeviCorrectionGroup g x u w
  + covRicciPairingRicciFirstSlotLeviCorrectionGroup g x u w
  + covRicciPairingRicciSecondSlotLeviCorrectionGroup g x u w
  = 0
```

using the same moving Gram inverse correction discipline as pinch-12.
