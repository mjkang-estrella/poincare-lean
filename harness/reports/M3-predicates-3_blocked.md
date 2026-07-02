# M3-predicates-3 blocked report

## Completed verified progress

### Step 1: basis-invariant trace bridge

Commit:

```text
3e6990cc Add basis-invariant metric trace bridge
```

Added the closed fiberwise algebraic trace bridge in
`Poincare/Global/ScalarVariation.lean`:

- `metricTraceInBasisAt`: metric trace of a fiberwise
  `LinearMap.BilinForm` in an arbitrary finite basis, paired with the
  `g`-raised dual coframe.
- `metricTraceEndomorphismAt`: the raised endomorphism
  `♯_g ∘ B`.
- `coord_eq_inner_metricDualVectorAt_of_basis`: arbitrary-basis coordinate
  covectors are metric pairings with their raised dual vectors.
- `metricTraceInBasisAt_eq_linearMap_trace`: the arbitrary-basis sum is
  `LinearMap.trace` of the raised endomorphism.
- `metricTraceInBasisAt_eq_metricTraceInBasisAt`: the sum is basis-independent.
- `metricTraceInBasisAt_finBasis_eq_traceMetricVariationAt` and
  `traceMetricVariationAt_eq_metricTraceInBasisAt`: the existing
  `traceMetricVariationAt` definition is the same trace when the raw fiber
  value of `h` is packaged as an honest bilinear form.

This discharges the purely algebraic basis-invariance part of the predecessor
plan without changing the frozen downstream predicate statements.

### Step 2: chart-frame specialization

Commit:

```text
88bc9466 Specialize metric trace to chart frame
```

Added a concrete chart-target basis and specialized the bridge:

- `chartTangentBasisAt`: transports `Module.finBasis ℝ E` through the
  derivative of the inverse chart at a chart target point.
- `chartTangentBasisAt_apply`: identifies each basis vector with
  `mfderivWithin ... ((extChartAt I x₀).symm) ... z` applied to the fixed
  model basis vector.
- `traceMetricVariationAt_eq_chartTangentBasisAt` and
  `traceMetricVariationAt_eq_chartTangentBasisAt_sum`: compute the closed trace
  in that chart frame.

This gives the intended smooth-frame *algebraic* specialization pointwise on
the target of `extChartAt`.

### Step 3: coframe raise rewrite

Commit:

```text
1df53ed6 Rewrite chart coframe via continuous raise
```

Added the raised-coframe rewrite needed before differentiability:

- `metricDualVectorAt_basisCoord_eq_metricRaiseContinuousAt`: for any finite
  basis coordinate covector, the algebraic raised vector equals
  `metricRaiseContinuousAt` applied to the continuous version of the covector.
- `metricDualVectorAt_chartTangentBasisAt_coord_eq_metricRaiseContinuousAt`:
  the chart-frame raised dual coframe has the same continuous-raise form.
- `traceMetricVariationAt_eq_chartTangentBasisAt_continuousRaise_sum`: the
  chart-frame trace sum is rewritten entirely using `metricRaiseContinuousAt`
  in the raised coframe slot.

This directly uses the M3-predicates-2 bridge
`metricDualVectorAt_eq_metricRaiseContinuousAt`.

## Remaining blocker

`TraceMetricVariationDerivAt` is still not honestly dischargeable from the
current closed layer.

The new chart-frame basis is pointwise and algebraic:

```lean
chartTangentBasisAt x₀ hz
```

It is defined by choosing a continuous linear equivalence from the proof that
the inverse-chart derivative is invertible. That is sufficient for basis
invariance and for rewriting the trace at a fixed chart target point, but it is
not a differentiable local frame field in the form needed to differentiate

```lean
z ↦ ∑ i, B z (frame_i z) (♯_z coframe_i z)
```

or to transport `RicciFlow.RicciFlow.fderiv_tensorMetricTrace_eq` back to

```lean
extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w
```

The missing non-vacuous pieces are:

1. A neighborhood-local chart frame field with stable proof terms, preferably
   defined directly from `mfderivWithin ... ((extChartAt I x₀).symm)` or from
   `VectorField.mpullback` of constant model fields, not from a pointwise
   `Classical.choose`.
2. A transported bilinear tensor field for a raw variation `h`, packaged as a
   differentiable/continuous-linear model family on the chart. This must be an
   actual regularity hypothesis or construction, not a proposition that simply
   restates `TraceMetricVariationDerivAt`.
3. Differentiability of the continuous raised chart coframe. The available
   rewrite now exposes the right shape, but the derivative proof still needs a
   local inverse-raise lemma in the chart metric, analogous to the
   `mdifferentiableAt_gradient` proof and the model
   `hasFDerivAt_inverse_raise` / `g_inverse_raise_metric_compat` chain.
4. A closed-to-model transport theorem identifying the derivative of the
   chart-frame trace with the closed `covTensor2DerivAt` contraction. Existing
   chart transport covers Levi-Civita values, but not yet this raw `(0,2)`
   variation trace derivative package.

Adding a hypothesis that directly states this derivative equality would merely
rename `TraceMetricVariationDerivAt`, so I stopped under the worker contract.

## Downstream state

No downstream consumer was made unconditional: `deltaGamma_innerTrace_eq'` and
`deltaGamma_innerTrace_eq_of_covTensor2Regular` still require the honest
`TraceMetricVariationDerivAt` input. The zero/static satisfiability witnesses
remain available:

- `traceMetricVariationDerivAt_zero`
- `traceMetricVariationDerivAt_const_timeDeriv`

## Verification

Commands run during the task:

```text
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result after each committed Lean unit: success, with only pre-existing linter
warnings.

No forbidden proof placeholders or unsafe evaluator constructs were added.
