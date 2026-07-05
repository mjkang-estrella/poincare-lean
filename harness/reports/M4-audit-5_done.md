# M4-audit-5 done / static-flow non-vacuity certificate

Read `harness/worker_contract.md` first.

## Result

The remaining scalar-flow predicate package is witnessed on the static
Ricci-flat flow `gt t = g`, assuming the actual bilinear Ricci-flat hypothesis
`forall y u w, g.ricciAt y u w = 0`.

The capstone theorem is:

```lean
satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_static_ricciFlat
```

It instantiates the headline scalar theorem chain end-to-end and proves:

```lean
SatisfiesHamiltonScalarEvolutionAt (fun _ : R => g) t0 x
```

The positive-scalar pinching side cannot be witnessed by a static Ricci-flat
metric because `SatisfiesPinchingQuotientEvolutionAt` contains `0 < R`.
For that side, the regularity-track members are witnessed for a static
positive-Einstein/space-form quotient identity by:

```lean
contMDiffAt_pinchingQuotientAt_two_of_ricciEndoAt_eq_smul_id
continuous_static_pinchingQuotientTrack_of_ricciEndoAt_eq_smul_id
```

A static positive-curvature space form is not a static solution of the
unnormalized Ricci flow unless Ricci vanishes, so the pointwise pinching
evolution predicate remains a separate positive-scalar mathematical input.

## Delivered names

- Time-regularity witnesses:
  - `hasDerivAt_metricRaiseContinuousAt_const`
  - `timeDerivAt_const_eq_zero_field`
  - `eventually_metricFlowRegularAt_const_and_ext_deriv`
  - `covTensor2ExtDifferentiableAt_timeDerivAt_const`
  - `covTensor2DerivExtDifferentiableAt_timeDerivAt_const`
- Static Ricci-flat flow package:
  - `ricciTraceAt_eq_zero_of_ricciAt_eq_zero`
  - `eventually_isClosedRicciFlowSolutionAt_const_and_extensionRegularAt_of_ricciAt_eq_zero`
  - `ricciVariationField_eq_zero_of_ricciAt_eq_zero`
  - `negTwoRicciVariationField_eq_zero_of_ricciAt_eq_zero`
- Static spatial regularity:
  - `contMDiffAt_scalarAt_two_of_ricciAt_eq_zero`
  - `scalarAt_extDerivFun_mDifferentiableAt_of_ricciAt_eq_zero`
  - `contMDiffAt_ricciNormSqAt_two_of_ricciAt_eq_zero`
  - `covTensor2DerivExtDifferentiableAt_ricciVariationField_of_ricciAt_eq_zero`
  - `ricciVariationField_divergence_mDifferentiableAt_of_ricciAt_eq_zero`
- Scalar-variation algebra/identity package:
  - `tensorDoubleDivergenceTimeDerivNegTwoRicciAt_const_of_ricciAt_eq_zero`
  - `traceMetricVariationLaplacianTimeDerivNegTwoRicciAt_const_of_ricciAt_eq_zero`
  - `tensorDoubleDivergenceNegTwoRicciLinearityAt_of_ricciAt_eq_zero`
  - `closedContractedBianchiAt_of_ricciAt_eq_zero`
  - `hamiltonScalarEvolutionTraceDerivativePredicatesAt_const_of_ricciAt_eq_zero`
  - `hamiltonScalarEvolutionPredicatesAt_const_of_ricciAt_eq_zero`
- Capstone:
  - `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_static_ricciFlat`
- Positive-scalar quotient-track regularity:
  - `contMDiffAt_pinchingQuotientAt_two_of_eq_const`
  - `continuous_static_pinchingQuotientTrack_of_eq_const`
  - `contMDiffAt_pinchingQuotientAt_two_of_ricciEndoAt_eq_smul_id`
  - `continuous_static_pinchingQuotientTrack_of_ricciEndoAt_eq_smul_id`

## Inventory

### `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`

| Hypothesis | Class | Witness status |
| --- | --- | --- |
| `[forall t, ContMDiffCovariantDerivative (gt t).leviCivita 1]` | spatial-canonical | inherited from the fixed closed metric instance in the static family |
| `hNearFlow` | algebraic-identity plus spatial-canonical | witnessed by `eventually_isClosedRicciFlowSolutionAt_const_and_extensionRegularAt_of_ricciAt_eq_zero` |
| `hreg : MetricFlowRegularAt` | time-regularity | witnessed by `metricFlowRegularAt_const`, bundled in `eventually_metricFlowRegularAt_const_and_ext_deriv` |
| `hgt : TimeDifferentiableAt` | time-regularity | witnessed by existing `timeDifferentiableAt_const` |
| `hRaise : HasDerivAt metricRaiseContinuousAt` | time-regularity | witnessed by `hasDerivAt_metricRaiseContinuousAt_const`, derivative `0` |
| `hDiv`, `hCon` | algebraic-identity | static delta-Gamma assembly witnesses from `ScalarVariation` discharge them; the trace-derivative bundle uses the existing const assembly lemmas |
| `hTraceGrad`, `hNegScalarGrad` | spatial-canonical | discharged in the primed theorem from static trace/scalar `C2`; scalar is identically zero |
| `hScalarDiff`, `hScalar2`, `hScalarExt2` | spatial-canonical | witnessed by zero scalar curvature lemmas above |
| `hRicDiff`, `hRicDivDiff` | spatial-canonical | canonical Ricci differentiability plus the Ricci-flat zero divergence witness |

### `hamilton_pinching_preserved` track

| Hypothesis | Class | Witness status |
| --- | --- | --- |
| `[CompactSpace M] [Nonempty M]` | spatial-canonical | structural maximum-principle assumptions; not produced by flow regularity |
| `[forall t, ContMDiffCovariantDerivative (gt t).leviCivita 1]` | spatial-canonical | inherited by static metric families |
| `hn : n = 3`, `hT0 : 0 <= T` | algebraic-identity | numeric assumptions |
| `hQ_cont` | spatial-canonical | witnessed for static pointwise-constant quotient tracks, and for the static Einstein quotient identity |
| `hQ2` | spatial-canonical | witnessed for static pointwise-constant quotient tracks, and for the static Einstein quotient identity |
| `hEvol` | algebraic-identity plus positive-scalar evolution | still conditional; it contains `0 < scalarAt` and a pointwise parabolic inequality |

## Honest-strength table

| Headline theorem | Status | Conditional on |
| --- | --- | --- |
| `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` | witnessed through the primed theorem on static Ricci-flat flow | bilinear Ricci-flatness of the fixed metric and the existing canonical covariant-derivative instance |
| `SatisfiesHamiltonScalarEvolutionAt` | witnessed end-to-end by `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_static_ricciFlat` | same Ricci-flat input |
| `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` | not witnessed by static Ricci-flat data | positive scalar, quotient differentiability, Ricci-evolution, scalar-evolution, and reaction/gradient inequality inputs |
| `hamilton_pinching_preserved` | track regularity witnessed for static constant/Einstein quotient tracks; full theorem still conditional | `hEvol`, compactness, nonemptiness, `n = 3`, and the time interval |
| `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow` | conditional | positive scalar, quotient/gradient bundles, Ricci/scalar evolution, and traceless reaction predicate |
| `hamilton_pinching_improvement` | conditional maximum-principle layer | same positive-scalar evolution predicate package plus compactness and interval assumptions |

## Commits

- `8836fbc9` M4 audit static scalar witnesses
- `24b53d9e` M4 audit static pinching track witnesses

## Verification

Commands run:

```bash
lake build Poincare.Global.ScalarEvolution
lake build Poincare.Global.ScalarEvolution
lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.MetricVariation
bash scripts/interface_audit.sh
```

Both one-module builds and the final requested three-module build succeeded
with existing warnings only.  The interface audit passed.  The direct
`scripts/interface_audit.sh` invocation is not executable in this worktree, so
the script was run through `bash`.
