# M4-prep-9 blocked

## Result

Route (a) was probed and partially landed in
`Poincare/Global/ScalarVariation.lean`.

Verified helper slices now available:

- `covTensor2SecondDerivAt_antisymm_expansion`
  expands the antisymmetrized closed second tensor derivative and cancels the
  differentiated-vector connection correction by
  `closedLeviCivita_extend_symm_at`.
- `covTensor2SecondDerivAt_pure_schwarz_cancel`
  proves the pure scalar-entry mixed second derivative block cancels by
  `extDerivFun_extDerivFun_extend_corrected_symm`.

These are the first two native closed-manifold reductions in the model proof
pattern before the tensor-slot correction terms are turned into curvature.

## Blocker

The full identity was not completed.  The missing closed-layer bridge is the
uncontracted product rule for differentiating tensor-slot correction fields of
the form

```lean
fun y => h y (g.leviCivita (extend E p) y (extend E v y)) (extend E q y)
fun y => h y (extend E p y) (g.leviCivita (extend E q) y (extend E v y))
```

The model proof uses `fderiv_tensor_corr_field`,
`fderiv_tensor_corr_field'`, and then
`christoffel_antisymm_deriv_eq_curvature` to expose the `dH * Gamma` terms,
cancel them against the two surviving slot corrections, and recognize the
curvature action.  The closed file currently has the curvature/Koszul
connection-entry machinery, but not the analogous uncontracted product-rule
bridge for an arbitrary raw `(0,2)` tensor field in moving canonical-extension
slots.

This is not a sign issue in `covTensor2SecondDerivCurvatureActionAt`; the
already-landed antisymmetry of that RHS matches the requested orientation.

## Next slice

1. Add closed analogues of `fderiv_tensor_corr_field` and
   `fderiv_tensor_corr_field'` for `CovTensor2ExtContMDiffAt h x 2`, stated in
   `extDerivFun`/canonical-extension form.
2. Add the closed analogue of
   `christoffel_antisymm_deriv_eq_curvature`, using the existing
   `closedCurvature_koszul` / connection-entry expansion stack to identify the
   antisymmetrized derivative of the slot connection field with
   `CovariantDerivative.curvatureOp`.
3. Combine those bridges with
   `covTensor2SecondDerivAt_antisymm_expansion` and
   `covTensor2SecondDerivAt_pure_schwarz_cancel` to prove
   `covTensor2SecondDerivAt ... u v ... - covTensor2SecondDerivAt ... v u ...`
   equals `covTensor2SecondDerivCurvatureActionAt`.
4. Specialize the resulting theorem to `ricciVariationField g`.

## Verification

- `lake build Poincare.Global.ScalarVariation` succeeded.
