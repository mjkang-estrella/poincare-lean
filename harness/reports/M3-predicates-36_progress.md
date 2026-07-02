# M3-predicates-36 progress report

## Summary

This session landed the first native closed contracted-Bianchi scaffolding in
`Poincare/Global/ScalarVariation.lean`, without changing the frozen predicate
statements.

Proved additions:

- `extDerivFun_traceMetricVariationAt_ricci`
- `covTensor2DerivAt_ricciVariationField_symm`
- `tensorDivergenceOneFormAt_ricciVariationField_swap`
- `closed_twice_contracted_bianchi_raw_of_first_contracted`
- `closed_twice_contracted_bianchi_trace_of_raw`
- `ClosedContractedBianchiOneFormAt.of_two_tensorDivergenceOneForm_eq_extDerivFun`
- `ClosedContractedBianchiOneFormAt.of_closed_trace_contraction`
- `ClosedContractedBianchiAt.of_closed_trace_contraction_near`

New native trace vocabulary:

- `closedCurvatureCovDerivAt`
- `closedCovRicciDerivAt`
- `closedCurvatureDivergenceAt`
- `closedRicciDivergenceTraceAt`
- `closedScalarContractionDerivTraceAt`

The raw contraction now mirrors the model theorem
`coord_twice_contracted_bianchi_raw`: a first-contracted Bianchi identity plus
the middle raised-curvature contraction gives the model-shaped
`2 * div Ric = dR` trace identity.  The final adapter shows exactly how the
nearby trace identities feed the frozen `ClosedContractedBianchiAt` consumer.

## Exact remaining native goals

The remaining target is still the native neighborhood one-form identity:

```lean
∀ᶠ y in nhds x, ClosedContractedBianchiOneFormAt g y
```

Using the new adapter, it is enough to prove these three near-`x` identities:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    closedRicciDivergenceTraceAt g y w
```

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  closedScalarContractionDerivTraceAt g y w =
    extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  2 * closedRicciDivergenceTraceAt g y w =
    closedScalarContractionDerivTraceAt g y w
```

The third identity should follow from the cyclic closed second-Bianchi core,
the raw contraction lemma, and the raised middle-term contraction.  The first
two identities are the remaining curvature/Ricci trace derivative expansion
bridges from the closed `covTensor2DerivAt` vocabulary to the new native
curvature-covariant derivative traces.

## Verification

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
forbidden-placeholder scan on the edited Lean modules
git diff --check
```

Results:

- Direct Lean file check: success, existing warnings only.
- Requested build: success, ending with `Build completed successfully (2806 jobs).`
- Forbidden-placeholder scan: no matches.
- Whitespace check: success.
