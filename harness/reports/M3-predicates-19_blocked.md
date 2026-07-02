# M3-predicates-19 blocked report

## Verified progress

This worker produced two proof-bearing commits.

1. Commit `73d7a100` adds the closed Schwarz infrastructure:
   - `extDerivFun_extDerivFun_extend_sub_swap_eq_bracket`
   - `extDerivFun_extDerivFun_extend_corrected_symm`

   The raw antisymmetrized mixed derivative is the derivative along the
   manifold Lie bracket of the two canonical extension fields.  The corrected
   version is the useful contraction-side identity: after subtracting the
   first-order Levi-Civita correction terms, the two mixed exterior derivatives
   swap by `hessianAt_symm'` and
   `extDerivFun_extDerivFun_extend_eq_hessianAt_add`.

2. Commit `5e984a95` adds
   `traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt`, a direct
   bridge from scalar `ContMDiffAt 2` regularity of
   `fun y => traceMetricVariationAt g h y` to
   `TraceMetricVariationExtSecondDifferentiableAt g h x`.

The focused check

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

succeeds after both commits, with only pre-existing linter warnings.

## Remaining exact obligations

The requested non-static contraction-side discharge is still blocked at the
Trace-C²-from-entry-vocabulary step.

The existing first-order Gram proof is pointwise at `x`:

```lean
traceMetricVariationAt_extDerivFun_eq_gram_rhs
gram_rhs_extDerivFun_eq_sum_product
gramMatrix_inv_extDerivFun_eq_neg_sum
gram_inv_deriv_contraction_eq_leviCivita_corrections
traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
```

That chain only needs a product rule for the exterior derivative at `x`.
The second-order predicate

```lean
TraceMetricVariationExtSecondDifferentiableAt g h x
```

instead asks for differentiability at `x` of the *field*

```lean
fun y =>
  extDerivFun (fun z => traceMetricVariationAt g h z) y (extend E w y)
```

To get this from the anchored Gram RHS, one must identify this field near `x`
with the derivative field of the finite Gram sum, then prove that derivative
field is differentiable at `x`.

The current entry vocabulary is not strong enough to justify the needed
neighborhood product-rule step.  The definitions

```lean
CovTensor2ExtSecondDifferentiableAt h x
MetricExtSecondDifferentiableAt g x
```

state differentiability at `x` of the already-formed derivative fields for
canonical scalar entries.  They do not state that the relevant scalar entries
are differentiable at all nearby `y`, so they do not let us apply
`CovariantDerivative.extDerivFun_mul` near `x` to rewrite the actual
derivative field of products such as

```lean
fun z =>
  (gramMatrix g x z)⁻¹ i j *
  h z (gramFrame x z i) (gramFrame x z j)
```

as

```lean
fun y =>
  (gramMatrix g x y)⁻¹ i j *
    extDerivFun (fun z => h z (gramFrame x z i) (gramFrame x z j)) y
      (extend E w y)
  +
  extDerivFun (fun z => (gramMatrix g x z)⁻¹ i j) y (extend E w y) *
    h y (gramFrame x y i) (gramFrame x y j)
```

In particular, the inverse-Gram side still needs the genuine C¹ field theorem

```lean
MDifferentiableAt I 𝓘(ℝ)
  (fun y =>
    extDerivFun (fun z => (gramMatrix g x z)⁻¹ i j) y (extend E w y)) x
```

derived from `MetricExtSecondDifferentiableAt g x`.  The existing
`gramMatrix_inv_extDerivFun_eq_neg_sum` is only the pointwise derivative
identity at `x`; it is not the field differentiability statement needed here.

## Needed next interface

One honest way forward is to strengthen the entry vocabulary with a local
neighborhood form, for example hypotheses that give the product-rule inputs
for the canonical scalar entries on a neighborhood of `x`, not only at `x`.
Another route is to derive scalar `ContMDiffAt 2` for the anchored Gram RHS
entries and then use the new
`traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt` bridge.

Once the trace C² predicate is supplied, the already-verified
`deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond` still requires the
separate moving-frame predicate

```lean
DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x
```

That predicate was not discharged in this worker.  It should be proved by a
field-level version of the first-slot trace identity, identifying the moving
basis derivative with `deltaGammaContractionDerivAt` and cancelling the
Levi-Civita correction terms.
