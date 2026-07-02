# M3-predicates-32 done report

## Result

The three algebraic substitution predicates now have proof-bearing discharge
lemmas in `Poincare/Global/ScalarVariation.lean`:

- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_eventually_eq`
- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_eventually_eq`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near`
- `TensorDoubleDivergenceNegTwoRicciLinearityAt.of_covTensor2Regular`

Supporting lemmas added:

- `ClosedSmoothRiemannianMetric.gradientAt_congr_of_eventuallyEq`
- `ClosedSmoothRiemannianMetric.hessianAt_congr_of_eventuallyEq`
- `ClosedSmoothRiemannianMetric.hessianDualAt_congr_of_eventuallyEq`
- `ClosedSmoothRiemannianMetric.laplacianAt_congr_of_eventuallyEq`
- `covTensor2DerivAt_congr_of_eventuallyEq`
- `covTensor2DerivAt_smul_field`
- `tensorDivergenceOneFormAt_congr_of_eventuallyEq`
- `tensorDivergenceOneFormAt_smul_field`
- `tensorDoubleDivergenceAt_congr_of_eventuallyEq`
- `tensorDoubleDivergenceAt_smul_field`

The near-flow field equality is now exposed as
`eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt`: a
neighborhood of pointwise closed Ricci-flow solutions plus extension
regularity gives the required `timeDerivAt = -2 Ric` field equality near `x`.

`Poincare/Global/ScalarEvolution.lean` now has the consolidated wrapper
`satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail`.
It derives all three algebraic substitution predicates internally.  The
remaining non-algebraic curvature predicate in that wrapper is
`ClosedContractedBianchiAt`; the other inputs are the regularity and assembly
data already used by the scalar-variation chain.

## Sanity check

Static/Ricci-flat case: the near-flow equality reduces to
`timeDerivAt = 0 = -2 Ric`, so the double-divergence and trace-Laplacian
substitutions collapse to the existing zero/static behavior.

Flat torus pattern: for a fixed Ricci-flat flat torus metric, the Ricci field
and scalar curvature vanish, so the new `-2 Ric` linearity and Laplacian
substitution both reduce to zero on the algebraic tail.  This is consistent
with the previous torus checks for the `δΓ` divergence blocks.

## Verification

Commands run:

```bash
lake env lean Poincare/Global/Laplacian.lean
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.Laplacian
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- `Poincare.Global.Laplacian` builds successfully.
- `Poincare.Global.ScalarVariation` builds successfully.
- `Poincare.Global.ScalarEvolution` builds successfully.
- The requested exact build target succeeds with existing linter warnings only.
