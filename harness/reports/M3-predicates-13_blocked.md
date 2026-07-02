# M3-predicates-13 blocked report

## Verified progress

`Poincare/Global/ScalarVariation.lean` now has the next proof-bearing pieces
of the Gram route:

1. `gramMatrix_extDerivFun_eq_spatialMetricDerivAt`
   and `gramMatrix_extDerivFun_eq_leviCivita`: differentiating a canonical
   Gram entry at the seed point is exactly the closed spatial metric
   derivative, hence the two Levi-Civita correction terms.
2. `extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections`: the flat
   derivative of `h` on canonical extension slots unfolds to
   `covTensor2DerivAt` plus the two Levi-Civita slot corrections.
3. A private `extDerivFun_sum_at` helper for finite sums of scalar functions.
4. `gram_rhs_extDerivFun_eq_sum_product`: the differentiated Gram RHS is now
   expanded by finite sums and the scalar product rule into

```lean
∑ i, ∑ j,
  ((gramMatrix g x x)⁻¹ i j *
    extDerivFun
      (fun y : M ↦ h y (gramFrame x y i) (gramFrame x y j)) x w
   + extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
      h x (gramFrame x x i) (gramFrame x x j))
```

This is the product-rule form isolated in
`M3-predicates-12_blocked.md`, now as a checked theorem.

## Remaining exact goal

The frozen predicate is still not discharged:

```lean
TraceMetricVariationDerivAt g h x
```

The remaining non-vacuous algebraic goal is the inverse-Gram cancellation.
After `gram_rhs_extDerivFun_eq_sum_product` and
`extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections`, the missing
identity is the pointwise contraction

```lean
∑ i, ∑ j,
  extDerivFun (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x w *
    h x (gramFrame x x i) (gramFrame x x j)
=
  - ∑ i, h x (g.leviCivita (extend E ((Module.finBasis ℝ (TM x)) i)) x w)
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))
  - ∑ i, h x ((Module.finBasis ℝ (TM x)) i)
      (g.leviCivita
        (extend E (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)))
        x w)
```

together with the routine expansion of the fixed inverse-Gram coefficients
into the raised dual basis.  This is the closed analogue of the model
inverse-raise metric-compatibility chain around
`hasFDerivAt_inverse_raise`, `g_inverse_raise_metric_compat`, and
`H_inverse_raise_trace`; that infrastructure is not yet available for the
closed canonical-extension Gram matrix.

## Verification

The current source check before this report was:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

It succeeded with only unused-section-variable warnings.
