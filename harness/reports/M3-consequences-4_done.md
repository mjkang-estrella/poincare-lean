# M3-consequences-4 done report

## Result

Implemented the time-tracked scalar lower-bound slice for compact closed
Ricci-flow tracks without placeholders.

New proof-bearing items:

- `scalarMinimumAt`
- `scalarMinimumTrack`
- `scalarMinimumAt_eq_of_isMinOn`
- `scalarMinimumAt_le_scalarAt`
- `closed_parabolic_min_principle_strict_var`
- `closed_parabolic_min_principle_var`
- `hamilton_scalar_lower_bound`
- `hamilton_scalar_nonneg_preserved`

## Notes

The scalar minimum is defined as the infimum of the scalar-curvature range.
Compactness and `exists_scalarAt_isMinOn` identify that infimum with an
attained minimum value.

The lower-bound proof mirrors the model argument by applying a compact
closed-manifold variable-coefficient minimum principle to
`R - c / (1 - (2/n)cτ)`.  The Laplacian-at-minimum step is discharged through
`laplacianAt_nonneg_of_isLocalMin`; the Hamilton reaction inequality supplies
`∂ₜR ≥ ΔR + (2/n)R²`.

The headline `c = 0` case is packaged as
`hamilton_scalar_nonneg_preserved`.

## Verification

Commands run:

```bash
lake build Poincare.MaximumPrinciple Poincare.Global.Laplacian Poincare.Global.ScalarVariation
lake env lean Poincare/Global/ScalarEvolution.lean
rg -n '<forbidden-placeholder regex>' Poincare/Global/ScalarEvolution.lean
git diff --check
lake build Poincare.Global.ScalarEvolution
```

Results:

- dependency rebuild succeeded after stale `.olean` interfaces were detected;
- focused `ScalarEvolution` Lean check succeeded;
- forbidden-placeholder scan returned no matches;
- whitespace check succeeded;
- exact requested module build succeeded, ending with
  `Build completed successfully (2806 jobs).`
