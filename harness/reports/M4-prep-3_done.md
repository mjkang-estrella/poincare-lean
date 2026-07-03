# M4-prep-3 done

## Definition correction

`Poincare/Global/ScalarVariation.lean` now preserves the refuted M4-prep-1
definition as `lichnerowiczFirstPairCurvatureAt`, with a correction-history
comment explaining that it traced the antisymmetric first curvature pair.

The live `lichnerowiczCurvatureAt` was replaced by the mixed Riemann/Ricci
contraction:

```lean
∑ i,
  h x
    (CovariantDerivative.curvatureOp g.leviCivita
      (extend E (b i)) (extend E u) (extend E w) x)
    (sharp i)
```

This matches the required `Σᵢ h(R(bᵢ,u)w, ♯bⁱ)` slot convention, so
`lichnerowiczLaplacianAt` and `SatisfiesRicciEvolutionAt` now consume the
corrected operator through the existing name.

## Immediate sanity gates

1. Constant sectional curvature: the old first-pair trace contained
   `R(eᵢ,eᵢ)` in an orthonormal frame and therefore vanished before the Ricci
   tensor could contribute. The corrected mixed contraction traces
   `R(eᵢ,u)w` against `eᵢ`, giving the Ricci/Riemann contraction expected on a
   nonflat space form, so the trace is no longer identically zero.
2. Flat/static: if curvature, Ricci, and the time variation vanish, the
   corrected mixed curvature term, the Ricci-action term, and
   `ricciQuadraticAt` vanish. The formal zero-tensor check is
   `lichnerowiczCurvatureAt_zero`.

## Trace validation surface

New declarations:

- `ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField`
- `lichnerowiczCurvatureAt_ricciQuadraticAt_trace_cancellation`
- `RoughTensorLaplacianRicciTraceAt`
- `RicciActionRicciTraceAt`
- `RicciEvolutionTraceRegularityAt`
- `ricciEvolutionTraceRegularityAt_firstOrder`
- `RicciEvolutionTraceIdentitiesAt`
- `ricciEvolution_rhs_trace_eq_hamilton_rhs`

The key corrected trace algebra is:

```lean
ricciQuadraticAt g x u w =
  2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
```

Therefore the traced `-2 * lichnerowiczCurvatureAt` term in the corrected
Lichnerowicz Laplacian cancels the explicit `ricciQuadraticAt` trace. With the
packaged obligations
`RoughTensorLaplacianRicciTraceAt` and `RicciActionRicciTraceAt`, the theorem
`ricciEvolution_rhs_trace_eq_hamilton_rhs` proves the Ricci-evolution RHS trace
has the Hamilton scalar shape:

```lean
g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x
```

## Roadmap update

M4-prep-2's blocked trace route is unblocked after the definition correction.
The remaining nontrivial work is to discharge the two packaged geometric trace
obligations:

1. `RoughTensorLaplacianRicciTraceAt`: metric trace of the rough Ricci
   Laplacian is the scalar Laplacian.
2. `RicciActionRicciTraceAt`: metric trace of the Ricci-endomorphism action on
   the Ricci field is `2 * |Ric|^2`.

The first-order Ricci-field regularity bridge is already formalized by
`ricciEvolutionTraceRegularityAt_firstOrder`; the second-order entrywise
regularity remains explicitly packaged in `RicciEvolutionTraceRegularityAt`.

## Verification

- `lake build Poincare.ChartIdentification` succeeded, refreshing the stale
  chart-identification artifact needed by `ScalarVariation`.
- `lake env lean Poincare/Global/ScalarVariation.lean` succeeded.
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  succeeded: `Build completed successfully (2806 jobs).`
- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean`
  returned no matches.
