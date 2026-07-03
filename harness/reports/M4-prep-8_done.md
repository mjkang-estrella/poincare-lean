# M4-prep-8 done

## Slice 6 assembly

`Poincare/Global/ScalarVariation.lean` now has the planned assembly theorem:

- `satisfiesRicciEvolutionAt_of_secondDerivCommutation`

Statement landed with the exact M4-prep-5 item-6 shape:

```lean
theorem satisfiesRicciEvolutionAt_of_secondDerivCommutation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hDeltaRic : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w)
        (deltaRicciSecondDerivContractionAt
          (gt t₀) (negTwoRicciVariationField (gt t₀)) x u w) t₀)
    (hComm : RicciSecondDerivCommutationAt (gt t₀) x) :
    SatisfiesRicciEvolutionAt gt t₀ x
```

The proof is the expected pointwise `HasDerivAt` derivative-value congruence:
`intro u w; simpa [SatisfiesRicciEvolutionAt, hComm u w] using hDeltaRic u w`.

## Curvature-commutation opening

Surveyed assets:

- Operator-level curvature backbone:
  `CovariantDerivative.curvatureOp_antisymm_apply`,
  `CovariantDerivative.curvatureOp_extend_add`,
  `CovariantDerivative.curvatureOp_extend_smul`,
  `CovariantDerivative.curvature_pair_antisymm_of_compat`,
  `CovariantDerivative.curvature_pair_symm`.
- Closed curvature derivative/Koszul assets:
  `closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction`,
  `closedCurvature_koszul`,
  `closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion`,
  `closedCurvatureCovDerivAt_antisymm`,
  `closed_cyclic_second_bianchi_at_of_inner_sum`,
  `eventually_closed_cyclic_second_bianchi`.
- Model-level Ricci-identity assets:
  `RicciFlow.covTensor2SndDeriv_ricci_identity`,
  `RicciFlow.covTensor2SndDeriv_comm`,
  `RicciFlow.connectionLaplacian_sub_transpose_eq_curvature`,
  `RicciFlow.connectionLaplacian_transpose_eq_add_curvature`.

I did not find an existing closed-manifold theorem of the exact shape

```lean
covTensor2SecondDerivAt g (ricciVariationField g) x u v p q
  - covTensor2SecondDerivAt g (ricciVariationField g) x v u p q
= curvature action on the two Ricci tensor slots
```

so the remaining discharge still needs the closed `covTensor2SecondDerivAt`
Ricci identity.

Landed first reusable slices toward that discharge:

- `closedCurvatureCovDerivAt_inner_koszul_expansion`
  names the single-entry scalar-paired curvature derivative after substituting
  `closedCurvature_koszul`.
- `covTensor2SecondDerivCurvatureActionAt`
  names the closed curvature-action RHS expected from the `(0,2)` tensor
  Ricci identity.
- `covTensor2SecondDerivCurvatureActionAt_antisymm`
  proves the action is antisymmetric in the two differentiated directions for
  any bilinear tensor field.
- `covTensor2SecondDerivCurvatureActionAt_ricciVariationField_antisymm`
  specializes that antisymmetry to the Ricci field.

## Remaining slice plan

1. Prove the closed `(0,2)` tensor Ricci identity:
   `covTensor2SecondDerivAt` antisymmetrized in its first two slots equals
   `covTensor2SecondDerivCurvatureActionAt`.  Either transport the model
   `covTensor2SndDeriv_ricci_identity` through the preferred chart/extend
   frame, or reproduce its proof using
   `extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion` and the
   closed curvature/Koszul entry lemmas.
2. Specialize that identity to `ricciVariationField g`.
3. Trace the identity over the basis/sharp pairings appearing in
   `deltaRicciSecondDerivContractionAt`; isolate the rough Laplacian, the
   Lichnerowicz curvature action, the Ricci-endomorphism action, and the
   `ricciQuadraticAt` term.
4. Package the traced result as `RicciSecondDerivCurvatureCommutationAt g x`.
5. Feed it through `RicciSecondDerivCommutationAt.of_closed_bianchi` and then
   through `satisfiesRicciEvolutionAt_of_secondDerivCommutation`.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean`
  returned no matches.
- `git diff --check` succeeded.
- `lake build Poincare.Global.ScalarVariation` succeeded, with existing
  warnings only.
