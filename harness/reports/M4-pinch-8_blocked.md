# M4-pinch-8 partial completion / Ricci-norm blocker

## Verified commits

- `973b4665` - `gradientAt_mul` and `gradient_mul`.
- `c847ee90` - `leviCivita_smul_function`.
- `719dff4c` - `hessianAt_mul`, `hessianContinuousAt_mul`,
  `laplacianAt_mul`, and `laplacianAt_mul'`.
- `328bc78b` - `scalarGradNormSqAt` and `laplacianAt_sq`.
- `616a897f` - scalar-square parabolic form
  `hasDerivAt_scalarAt_sq_of_satisfiesHamiltonScalarEvolutionAt`.

Each committed unit was checked with the relevant narrow build before commit:

```bash
lake build Poincare.Global.Laplacian
lake build Poincare.Global.ScalarEvolution
```

## Completed scalar payoff

The closed scalar product-rule layer is now available in
`Poincare/Global/Laplacian.lean`:

```lean
ClosedSmoothRiemannianMetric.gradientAt_mul
ClosedSmoothRiemannianMetric.leviCivita_smul_function
ClosedSmoothRiemannianMetric.hessianAt_mul
ClosedSmoothRiemannianMetric.laplacianAt_mul
ClosedSmoothRiemannianMetric.laplacianAt_sq
ClosedSmoothRiemannianMetric.scalarGradNormSqAt
```

The scalar-square parabolic identity is proved in
`Poincare/Global/ScalarEvolution.lean`:

```lean
hasDerivAt_scalarAt_sq_of_satisfiesHamiltonScalarEvolutionAt
```

It states the honest closed form

```lean
HasDerivAt (fun t => (gt t).scalarAt x ^ 2)
  ((gt t0).laplacianAt (fun y => (gt t0).scalarAt y ^ 2) x
    - 2 * (gt t0).scalarGradNormSqAt x
    + 4 * (gt t0).scalarAt x * (gt t0).ricciNormSqAt x) t0
```

from `SatisfiesHamiltonScalarEvolutionAt` and `C^2` spatial scalar regularity.

## Remaining blocker: Ricci-norm Bochner payoff

The requested Ricci-norm payoff needs the spatial Bochner identity

```lean
(gt t0).laplacianAt (fun y => (gt t0).ricciNormSqAt y) x
  =
    2 * <roughTensorLaplacianAt Ric, Ric>_g x
      + 2 * covRicciNormSqAt (gt t0) x
```

in closed-manifold vocabulary.

The current closed trace machinery proves:

- `covRicciNormSqAt` and `covRicciNormSqAt_nonneg`.
- `RoughTensorLaplacianRicciTraceAt`, which traces the rough Ricci Laplacian
  linearly to the scalar Laplacian.
- `RicciActionRicciTraceAt`, which traces the Ricci action linearly to
  `2 * ricciNormSqAt`.
- time-derivative formulas for `ricciNormSqAt`, including
  `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt`.

What is still missing is the second-order spatial product/trace bridge for
the quadratic Ricci trace

```lean
ricciNormSqAt = trace (Ric# o Ric#)
```

as a function of the base point.  The scalar product rule proves the analogous
scalar formula, but it does not by itself differentiate the moving-fiber,
metric-raised tensor trace `trace (Ric# o Ric#)` through `laplacianAt`.

I did not add a fake assumption-packaged theorem for this, because the contract
forbids vacuous statement layers.  The next proof unit should build the missing
non-vacuous bridge:

1. Define a closed rough-Ricci pairing term, e.g. the metric trace pairing of
   `roughTensorLaplacianAt g (ricciVariationField g)` with `ricciVariationField g`.
2. Prove first spatial derivative of `ricciNormSqAt` from the derivative of
   `ricciVariationField` plus the metric-compatibility cancellation for the
   raise/lower maps.
3. Prove the second derivative trace identity for `ricciNormSqAt`, yielding the
   coefficients `2` and `2` in the Bochner formula.
4. Combine that identity with `covRicciNormSqAt_nonneg` and the existing
   `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt` layer to state the
   parabolic inequality.

