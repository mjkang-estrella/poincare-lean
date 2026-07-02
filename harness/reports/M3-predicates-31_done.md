# M3-predicates-31 done report

## Result

The positive `(T1 + T2)` block is now proved in
`Poincare/Global/ScalarVariation.lean`:

```lean
deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
  (gt t₀) (timeDerivAt gt t₀) x
= tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
```

New proof-bearing theorems:

- `covTensor2SecondDerivAt_add_outer`
- `covTensor2SecondDerivAt_smul_outer`
- `covTensor2SecondDerivAt_add_inner`
- `covTensor2SecondDerivAt_smul_inner`
- `covTensor2SecondDerivAt_add_left`
- `covTensor2SecondDerivAt_smul_left`
- `covTensor2SecondDerivAt_add_right`
- `covTensor2SecondDerivAt_smul_right`
- `covTensor2SecondDerivAt_timeDeriv_divergence_trace_eq`
- `tensorDoubleDivergenceAt_eq_sum_sum_positive_T2`
- `deltaGammaDivergenceTraceSecondDerivPositiveBlockAt_eq_tensorDoubleDivergenceAt`
- `deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular`

The proof follows the model sub-identity (a).  The inner trace of the
second-derivative block is identified with the covariant derivative of
`tensorDivergenceOneFormAt` via the first-order trace machinery, then the
outer trace is rewritten as `tensorDoubleDivergenceAt`.  The transposed
positive summands agree under the double trace using
`sum_metricDualVectorAt_contraction_swap`, so the `1 / 2` factor is absorbed.

The explicit positive-block hypothesis in
`deltaGammaDivergenceTraceHessianAssemblyAt_of_positiveBlock` is discharged by
`deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular`.

## Torus sanity check

The flat two-torus pattern from `M3-predicates-29_blocked.md` matches this
identity.  For `h_11 = cos y` at `y = 0`, the positive block is
`div div h = partial_1 partial_1 h_11 = 0`.  The already-proved trace block is
`Delta(tr h) = -1`, so the grouped expression remains
`0 - 1 / 2 * (-1) = 1 / 2`, matching the summed delta-Gamma divergence trace.

## Remaining list

The trace block and positive block are closed, and the divergence Hessian
assembly is discharged from honest regularity hypotheses.  The remaining
non-regularity/algebraic frontier is exactly:

- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt`
- `TensorDoubleDivergenceNegTwoRicciLinearityAt`
- `ClosedContractedBianchiAt`

## Verification

Commands run:

```bash
rg -n '\b(sorry|axiom|native_decide)\b' \
  Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- no `sorry`, `axiom`, or `native_decide` matches in the checked Lean files;
- focused Lean check succeeds;
- the exact requested build target succeeds, with linter warnings only.
