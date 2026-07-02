# M3-predicates-38 progress report

## Summary

Landed a verified closed Ricci derivative expansion adapter in
`Poincare/Global/ScalarVariation.lean`.

New native vocabulary:

- `ClosedRicciDerivativeExpansionAt`
- `covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt`

The new expansion predicate is the moving-point exterior derivative form:

```lean
extDerivFun (fun y ↦ g.ricciAt y (extend E u y) (extend E w y)) x v =
  closedCovRicciDerivAt g x v u w
    + g.ricciAt x (g.leviCivita (extend E u) x v) w
    + g.ricciAt x u (g.leviCivita (extend E w) x v)
```

From that exact derivative expansion, the requested covariant tensor derivative
atom is now proved:

```lean
covTensor2DerivAt g (ricciVariationField g) x v u w =
  closedCovRicciDerivAt g x v u w
```

## Bridges chained

Bridge (1), pointwise and neighborhood form:

- `tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt`
- `eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt`

Bridge (2), pointwise and neighborhood form:

- `closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt`
- `eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt`

Supporting Ricci bilinear packaging was added for the existing Gram trace
theorem:

- `tensor2AddLeft_ricciVariationField`
- `tensor2SMulLeft_ricciVariationField`
- `tensor2AddRight_ricciVariationField`
- `tensor2SMulRight_ricciVariationField`
- `ricciVariationBilinForm`

## Remaining exact state

The analytic content now isolated for bridges (1) and (2) is:

```lean
∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

Bridge (2) also consumes the already-standard entry differentiability:

```lean
∀ᶠ y in nhds x, CovTensor2ExtDifferentiableAt (ricciVariationField g) y
```

Bridge (3) remains the same as in `M3-predicates-37_blocked.md`: prove the
closed first-contracted second-Bianchi identity for `closedCurvatureCovDerivAt`
and the raised middle-term contraction identifying the curvature-divergence
trace with `closedRicciDivergenceTraceAt`.

## Verification

```bash
lake env lean Poincare/Global/ScalarVariation.lean
forbidden-placeholder scan on ScalarVariation and ScalarEvolution
git diff --check
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- Direct Lean file check: success, existing warnings only.
- Forbidden-placeholder scan on the two Lean modules: no matches.
- Whitespace check: success.
- Requested two-module build: success, ending with
  `Build completed successfully (2806 jobs).`
