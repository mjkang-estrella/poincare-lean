# M3-predicates-34 blocked report

## Summary

The unconditional closed one-form identity

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

was not closed in this session.

Verified Lean progress was kept deliberately small and non-vacuous in
`Poincare/Global/ScalarVariation.lean`:

- `ClosedContractedBianchiOneFormAt`
- `ClosedContractedBianchiAt.of_oneForm_near`

The new predicate names the exact intrinsic one-form identity `div Ric = 1/2 dR`.
The wrapper proves that a local neighborhood proof of this named predicate feeds
the existing reducer
`ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near`.

## Current reduced goal

The remaining mathematical target is now:

```lean
∀ᶠ y in nhds x, ClosedContractedBianchiOneFormAt g y
```

plus the already-existing scalar regularity side conditions required by
`ClosedContractedBianchiAt.of_oneForm_near`.

Unfolded, this is exactly:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

## Why the model theorem cannot yet be fired directly

The coordinate theorem already has the desired mathematical content:

```lean
RicciFlow.RicciFlow.ricciDivergence_eq_half_fderiv_scalar
```

and the self-contained wrapper:

```lean
RicciFlow.fderiv_coordScalar_eq_two_ricciDivergenceForm_of_contDiff
```

However, the closed definitions are intrinsic:

- `g.ricciAt` is `CovariantDerivative.ricciBilinearAt g.leviCivita`.
- `g.scalarAt` is `CovariantDerivative.scalarCurvatureAt g.leviCivita`.
- `tensorDivergenceOneFormAt g (ricciVariationField g)` is built from
  `covTensor2DerivAt` using canonical `extend E` sections and the tangent-fiber
  metric-dual basis.

The model theorem is phrased for a model metric family `G : E -> E ->L[ℝ] E ->L[ℝ] ℝ`,
using `coordRicci`, `coordScalar`, and `ricciDivergence`.

The current repo has the local chart-transport connection regularity route:

- `CovariantDerivative.blendedChartMetric`
- `LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed`
- `LeviCivitaExistence.closedLeviCivitaConnection_contMDiff`

but I did not find verified bridge lemmas transporting the full Ricci/scalar
divergence stack back to the intrinsic closed definitions.

## Exact missing bridge lemmas

For a chart center `x0`, a cutoff metric `Ghat =
CovariantDerivative.blendedChartMetric χ G0 g.inner x0`, and `z` near
`extChartAt I x0 x0`, the next worker should prove chart bridges of the form:

1. Ricci bridge:

```lean
g.ricciAt ((extChartAt I x0).symm z) p q
= RicciFlow.RicciFlow.coordRicci Ghat z p_chart q_chart
```

with `p_chart` and `q_chart` the chart-coordinate representatives of the
tangent vectors.

2. Scalar bridge:

```lean
g.scalarAt ((extChartAt I x0).symm z)
= RicciFlow.RicciFlow.coordScalar Ghat z
```

3. Ricci divergence bridge:

```lean
tensorDivergenceOneFormAt g (ricciVariationField g)
  ((extChartAt I x0).symm z) w
= RicciFlow.RicciFlow.ricciDivergence Ghat z w_chart
```

4. Exterior derivative bridge:

```lean
extDerivFun (fun y : M ↦ g.scalarAt y)
  ((extChartAt I x0).symm z) w
= fderiv ℝ (fun z : E ↦ RicciFlow.RicciFlow.coordScalar Ghat z) z w_chart
```

Once these are available near `x`, the model theorem should discharge
`ClosedContractedBianchiOneFormAt g y`, and then
`ClosedContractedBianchiAt.of_oneForm_near` fires the frozen consumer.

## Sanity checks

- Static flat metrics still give both sides zero.
- The new predicate is not a certificate or placeholder: it is the exact
  one-form identity required by the prior reducer.
- No frozen target statement was changed.

## Verification

Forbidden-placeholder scan on the edited Lean file:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ScalarVariation.lean
```

Result: no matches.

Whitespace check:

```bash
git diff --check
```

Result: success.

Requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success.  The build completed with existing linter warnings and ended
with:

```text
Build completed successfully (2806 jobs).
```
