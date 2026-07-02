# M3-predicates-18 blocked report

## Verified progress

`Poincare/Global/ScalarVariation.lean` now contains a proof-bearing
contraction-side reduction package:

1. Added the honest scalar second-derivative predicate
   `TraceMetricVariationExtSecondDifferentiableAt g h x`.
2. Replayed the existing first-order first-slot theorem at the field level:
   `deltaGammaFirstSlotTraceFieldAt_eq_half_trace_extDerivFun`.
3. Promoted that identity to a neighborhood statement:
   `deltaGammaFirstSlotTraceFieldAt_eventually_eq_half_trace_extDerivFun`.
4. Proved first-slot field differentiability from the neighborhood identity and
   scalar trace C²:
   `deltaGammaFirstSlotTraceFieldDifferentiableAt_of_trace_extSecond`.
5. Added the closed Hessian compatibility lemma
   `extDerivFun_extDerivFun_extend_eq_hessianAt_add`.
6. Proved the contraction-side field Hessian predicate from the local
   first-order identity, scalar trace C², and gradient differentiability:
   `deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond`.
7. Added the frozen-bridge wrapper
   `deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_trace_extSecond`,
   which discharges `DeltaGammaContractionTraceHessianDerivativeAt` once the
   existing `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt` predicate and
   the scalar C² obligations are supplied.

The source check

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

succeeds with only pre-existing linter warnings.

## Remaining exact obligations

The full requested non-static contraction-side discharge is not complete.  Two
genuine analytic/Gram obligations remain.

First, derive

```lean
TraceMetricVariationExtSecondDifferentiableAt
  (gt t₀) (timeDerivAt gt t₀) x
```

from the existing entrywise C² vocabulary
`CovTensor2ExtSecondDifferentiableAt` and `MetricExtSecondDifferentiableAt`.
This is the second-order replay of the Gram RHS: differentiate

```lean
∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
  timeDerivAt gt t₀ y (gramFrame x y i) (gramFrame x y j)
```

once more and prove the resulting derivative field is differentiable at `x`.
This requires a C¹ theorem for the inverse-Gram derivative entries, not just
the already proved first derivative identity
`gramMatrix_inv_extDerivFun_eq_neg_sum`.

Second, prove the moving-basis field-covariant-derivative predicate

```lean
DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x
```

from the same Gram field formula.  This is not definitionally immediate:
`deltaGammaContractionDerivAt` differentiates the traced vector-valued
`δΓ` tensor through `covDeltaGammaDerivAt`, while
`deltaGammaFirstSlotTraceFieldAt` traces over the moving tangent basis.  The
missing proof must identify those two derivatives via the two-point Gram frame
and cancel the Levi-Civita corrections.

## Schwarz / mixed-derivative gap

The expected second derivative of the scalar entries contains terms of the
form

```lean
extDerivFun
  (fun y ↦
    extDerivFun
      (fun z ↦ timeDerivAt gt t₀ z (extend E p z) (extend E q z))
      y (extend E v y))
  x u
```

The final identification with the closed Hessian/covariant derivative needs
the corresponding mixed-derivative symmetry for closed `extDerivFun` scalar
entries.  I did not find an existing closed lemma in this file that provides
that Schwarz step for these canonical-extension scalar functions.

## Verification

Verified before writing this report:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with only existing linter warnings.
