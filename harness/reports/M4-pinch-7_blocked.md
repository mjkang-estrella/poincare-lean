# M4-pinch-7 blocked

## Verified partial progress

- Added `metricOrthogonalBasisAt`, `covRicciNormSqAt`,
  `covRicciNormSqAt_eq_metricOrthogonalBasis_sum`, and
  `covRicciNormSqAt_nonneg` in `Poincare/Global/ScalarVariation.lean`.
- `covRicciNormSqAt` is the metric-orthogonal-frame triple contraction of
  `covTensor2DerivAt g (ricciVariationField g)`, with the diagonal metric
  weights divided out.
- `covRicciNormSqAt_nonneg` is proved by reducing the expression to a finite
  sum of nonnegative square-over-positive-weight terms.
- Verified with:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm
```

## Blocker

The remaining requested Bochner and scalar-square parabolic forms require
closed-manifold product-rule infrastructure that is not currently present in
the target modules.

For the Ricci norm Bochner layer, the requested identity

```lean
g.laplacianAt (fun y => g.ricciNormSqAt y) x
  = 2 * <roughTensorLaplacianAt Ric, Ric> + 2 * covRicciNormSqAt g x
```

requires differentiating the quadratic trace
`ricciNormSqAt = trace (Ric# o Ric#)` twice in space.  The current trace-commute
machinery proves trace statements for linear tensor fields such as
`traceMetricVariationAt g H` and the rough tensor Laplacian trace, but it does
not yet provide the second-order product rule for the quadratic Ricci trace.

For the scalar-square parabolic form, the derivative part can come from
`SatisfiesHamiltonScalarEvolutionAt`, but rewriting it as

```lean
d/dt R^2 = laplacianAt (fun y => (g.scalarAt y)^2) x
  - 2 * |grad R|^2 + 4 * R * |Ric|^2
```

requires the closed scalar product formula

```lean
laplacianAt (fun y => f y * f y) x
  = 2 * f x * laplacianAt f x + 2 * <gradientAt f, gradientAt f>
```

or a corresponding `laplacianAt_mul` theorem.  `Poincare/Global/Laplacian.lean`
currently has `laplacianAt_add`, `laplacianAt_const_smul`, and
`laplacianAt_const`, but no closed `laplacianAt_mul` or `hessianAt_mul`.

## Evidence checked

- `Poincare/Global/Laplacian.lean` has scalar gradient, Hessian, Laplacian,
  additivity, constant scaling, and constant rules only.
- `Poincare/ModelLaplacian.lean` has the model-space product theorem
  `RicciFlow.modelLaplacian_mul`; there is no closed analogue wired to
  `ClosedSmoothRiemannianMetric.laplacianAt`.
- `roughTensorLaplacianAt`, `ricciEvolutionTensorRHSAt`, and the existing
  trace identities are present in `Poincare/Global/ScalarVariation.lean`, but
  they trace linear tensor fields, not the quadratic Ricci norm function.

## Next proof unit

The next safe theorem layer is a closed product-rule patch:

1. Prove `gradientAt_mul` from `CovariantDerivative.extDerivFun_mul`.
2. Prove the variable scalar times vector-field covariant derivative rule
   needed by `hessianAt_mul`.
3. Derive `hessianAt_mul` and `laplacianAt_mul`.
4. Specialize `laplacianAt_mul` to `f = scalarAt` for the scalar-square
   parabolic rewrite, then use the same product-rule layer for the
   second-order Ricci-norm Bochner expansion.
