# M4-prep-14 blocked report

## Status

Blocked before discharging `RicciSecondDerivCurvatureCommutationAt g x`.

Verified partial commits:

- `1242d333` — `M4-prep-14: add Ricci second derivative symmetry`
- `8e07e431` — `M4-prep-14: trace Ricci contraction cancellation`
- `88eac69f` — `M4-prep-14: assemble Ricci evolution chain`

## Verified work landed

1. Added `covTensor2SecondDerivAt_ricciVariationField_symm`.
   This proves the Ricci field remains symmetric in the two tensor slots after
   one closed second covariant derivative.

2. Added
   `covTensor2SecondDerivAt_ricciVariationField_trace_swap_inner_left`.
   This is the raised-dual-basis contraction swap needed for the
   `deltaRicciSecondDerivContractionAt` trace over the inner derivative slot and
   first tensor slot.

3. Added
   `deltaRicciSecondDerivContractionAt_ricciVariationField_trace_cancel`.
   This removes the duplicate contraction block in the Ricci-field
   specialization of `deltaRicciSecondDerivContractionAt`, using the new
   second-derivative symmetry and `sum_metricDualVectorAt_contraction_swap`.

4. Added
   `satisfiesRicciEvolutionAt_of_ricciFlow_curvatureCommutation`.
   This fires the downstream chain from a supplied
   `RicciSecondDerivCurvatureCommutationAt (gt t₀) x`: the canonical
   `eventually_closed_cyclic_second_bianchi` feeds
   `RicciSecondDerivCommutationAt.of_closed_bianchi`, and the mainline
   delta-Ricci second-derivative bridge feeds
   `satisfiesRicciEvolutionAt_of_secondDerivCommutation`.

## Blocking point

After the verified trace cancellation, the remaining untraced tensor identity
still contains the two divergence-second-derivative blocks with free tensor
slots, together with the H-slot trace block

```lean
∑ i, covTensor2SecondDerivAt g (ricciVariationField g) x (b i) u w (sharp i)
∑ i, covTensor2SecondDerivAt g (ricciVariationField g) x (b i) w u (sharp i)
∑ i, covTensor2SecondDerivAt g (ricciVariationField g) x u w (b i) (sharp i)
```

The scalar trace route has the necessary traced derivative of the one-form
contracted Bianchi identity, via
`ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near`
and `tensorDoubleDivergenceAt`.  I did not find the corresponding pointwise
untraced bridge

```lean
∀ u w : TM x,
  ∇_u ((div Ric)(w)) =
    (1 / 2) * g.hessianAt (fun y => g.scalarAt y) x u w
```

in the closed API.  That free-slot differentiated one-form Bianchi bridge is
needed to cancel the remaining Hessian terms and isolate the frozen
rough/curvature/Ric-action/quadratic RHS of
`RicciSecondDerivCurvatureCommutationAt`.

Per the worker contract, I stopped rather than introduce an identity hypothesis
or weaken the frozen target.

## Verification

Commands run:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
rg -n '\b(sorry|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean
git diff --check
```

Results:

- `lake env lean Poincare/Global/ScalarVariation.lean` succeeded.
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  succeeded.
- no `sorry`, `axiom`, or `native_decide` was introduced in
  `Poincare/Global/ScalarVariation.lean`.
- `git diff --check` passed before each commit.
