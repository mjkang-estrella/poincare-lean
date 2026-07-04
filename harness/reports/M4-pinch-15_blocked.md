# M4-pinch-15 partial progress / verification-time blocker

## Verified local progress

Implemented in `Poincare/Global/ScalarVariation.lean` and committed as
`1d932fc5`:

- `covRicciPairingRicciCovariantGroup`
- `covRicciPairingRicciFirstSlotLeviCorrectionGroup`
- `covRicciPairingRicciSecondSlotLeviCorrectionGroup`
- `covRicciPairingRicciDerivGroup_eq_covariant_plus_leviCorrections`

The split follows the pinch-12 Ricci-entry derivative pattern, using
`closedRicciDerivativeExpansionAt_canonical` on the differentiated Ricci entry.

Cheap hygiene checks passed after the edit:

```bash
git diff --check
rg -n '\b(sorry|admit|axiom|native_decide)\b' \
  Poincare/Global/ScalarVariation.lean \
  Poincare/Global/RicciNorm.lean \
  Poincare/Global/ScalarEvolution.lean
```

## Verification boundary

`lake build Poincare.Global.ScalarVariation` was attempted twice. The first run
replayed dependencies and warmed stale `RicciNorm` artifacts that initially made
direct-file checking report missing pinching/RicciNorm declarations. The second
run again replayed dependencies, reached the final `ScalarVariation` module, and
then remained silent for an extended period with no diagnostics from the changed
block. I terminated the specific build process rather than leave a runaway
session active.

No full `lake build` success is claimed.

## Literal next goal

Prove the six-group cancellation:

```lean
theorem covRicciPairing_gram_inv_deriv_groups_cancel_leviCorrections
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    covRicciPairingGramInvFirstDerivGroup g x u w
      + covRicciPairingGramInvSecondDerivGroup g x u w
      + covRicciPairingFirstSlotLeviCorrectionGroup g x u w
      + covRicciPairingSecondSlotLeviCorrectionGroup g x u w
      + covRicciPairingRicciFirstSlotLeviCorrectionGroup g x u w
      + covRicciPairingRicciSecondSlotLeviCorrectionGroup g x u w
      = 0 := by
  ...
```

Use the pinch-12 cancellation discipline:

- build covariant-Ricci analogues of the two inverse-Gram contraction tensors;
- rewrite inverse-Gram derivatives with `gram_inv_deriv_contraction_eq_leviCivita_corrections`
  or directly with `gramMatrix_inv_extDerivFun_eq_neg_sum` plus
  `spatialMetricDerivAt_eq_leviCivita`;
- identify the four produced slot-correction sums with
  `covRicciPairingFirstSlotLeviCorrectionGroup`,
  `covRicciPairingSecondSlotLeviCorrectionGroup`,
  `covRicciPairingRicciFirstSlotLeviCorrectionGroup`, and
  `covRicciPairingRicciSecondSlotLeviCorrectionGroup`;
- finish by rewriting and `ring`.
