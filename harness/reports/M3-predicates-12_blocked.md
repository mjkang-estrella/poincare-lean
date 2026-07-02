# M3-predicates-12 blocked report

## Verified progress

The Gram-matrix route now has proof-bearing source progress in
`Poincare/Global/ScalarVariation.lean`:

1. `gramMatrix`, `gramMatrix_at_base`, base determinant nonvanishing/unit, and
   entry differentiability via canonical extensions.
2. Determinant differentiability, eventual invertibility near the seed point,
   adjugate-entry differentiability, and inverse-entry differentiability:
   `gramMatrix_eventually_isUnit`, `gramMatrix_inv_entry_mdiffAt`.
3. Canonical extension frame basis construction from Gram invertibility:
   `gramFrame`, `gramFrame_linearIndependent_of_isUnit`, `gramFrameBasis`.
4. Raised-dual coframe and trace identity:
   `metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv` and
   `traceMetricVariationAt_eq_sum_gram_inv`.
5. Scalar differentiability half:
   `traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt` and
   `traceMetricVariationAt_extDerivFun_eq_gram_rhs`.

All of these use the canonical extension frame.  The raw constant tangent
section route from `M3-predicates-11` was not used.

## Remaining exact goal

The nonzero closed trace-derivative predicate is still not discharged:

```lean
TraceMetricVariationDerivAt g h x
```

unfolding to:

```lean
∀ w : TM x,
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ∑ i, covTensor2DerivAt g h x w ((Module.finBasis ℝ (TM x)) i)
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)))
  =
    extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w
```

The new Gram derivative bridge reduces the right side to:

```lean
extDerivFun
  (fun y : M ↦
    ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
      h y (gramFrame x y i) (gramFrame x y j)) x w
```

The remaining proof is the explicit product-rule expansion of this scalar RHS
followed by the covariant cancellation:

```lean
∑ i, ∑ j,
  ((gramMatrix g x x)⁻¹ i j *
    extDerivFun
      (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
   + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
      h x (gramFrame x x i) (gramFrame x x j))
```

against the contracted `covTensor2DerivAt` expression and the derivative of
the inverse Gram matrix.  I did not finish this algebraic/covariant
identification in this task.

## Why this is the next blocker

The file has the metric-compatibility ingredients for the canonical extension
sections (`spatialMetricDerivAt_eq_leviCivita` and
`spatialMetricDualVectorDerivAt_inner_apply`), and the Gram route now provides
the differentiable moving frame.  What remains is to connect the derivative of
the inverse Gram entries to the raised-index Levi-Civita correction terms and
then sum-cancel those terms against the two connection corrections in
`covTensor2DerivAt`.

This is not the old raw-section blocker: the scalar functions are now
differentiable.  The remaining gap is the product-rule/covariant cancellation
lemma needed to turn the scalar derivative into the exact
`TraceMetricVariationDerivAt` contraction.

## Verification

The final source check before this report was:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

It succeeded with only pre-existing unused-section-variable warnings.
