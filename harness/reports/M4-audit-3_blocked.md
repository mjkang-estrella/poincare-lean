# M4-audit-3 blocked / use-site survey

Read `harness/worker_contract.md` first.

## Executive result

The expected all-local outcome is not true for the current Lean interface.
Most downstream M4 uses of `ClosedRicciFlowExtensionRegularAt` are
eventual-neighborhood substitutions, but the first bridge theorem consumes the
extension-field regularity as a genuinely global admissibility proof:

```lean
isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt
```

At `Poincare/Global/MetricVariation.lean:244-248`, the proof destructs
`hext v` into `hZ` and passes `hZ` to
`isClosedRicciFlowSolutionAt_timeDerivAt`.  That theorem in turn calls
`hflow.flow hZ hreg w`.

This is global because the underlying flow field is:

```lean
flow : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 2 (T% Z) →
  ∀ (hreg : DerivRegularAt (cov t₀) Z x) ...
```

from `Poincare/RicciFlowEquation.lean:55-58`.  The closed wrapper
`IsClosedRicciFlowSolutionAt` is currently just this predicate specialized to
closed metrics (`Poincare/Global/RicciFlow.lean:40-43`).

Mathlib's `extend` API supplies exactly the local facts:

- `exists_contMDiffOn_extend`: `∃ s ∈ 𝓝 x₀, ContMDiffOn ... (extend F σ₀) s`
- `contMDiffAt_extend'`: `CMDiffAt k (T% (extend F σ₀)) x`

It does not supply `CMDiff 2 (T% (extend E v))` globally.  Therefore replacing
the bundle field with only `CMDiffAt`/eventual local smoothness would leave the
call to `hflow.flow` untypeable.

## Use-site survey

Grep target:

```bash
rg -n "ClosedRicciFlowExtensionRegularAt" \
  Poincare/Global/MetricVariation.lean \
  Poincare/Global/ScalarVariation.lean \
  Poincare/Global/ScalarEvolution.lean
```

| Site | Role | Regularity use |
| --- | --- | --- |
| `MetricVariation.lean:210` `ClosedRicciFlowExtensionRegularAt` | Definition | Global by definition: `ClosedC2TangentField (extend E v)` plus `DerivRegularAt`. |
| `MetricVariation.lean:224` `closedRicciFlowExtensionRegularAt_const_of_closedC2_extend` | Constructor/witness under explicit global hypothesis | Global; it assumes exactly `∀ v, ClosedC2TangentField (extend E v)`. |
| `MetricVariation.lean:238` `isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt` | Direct theorem consumer | **Global blocker.** `hZ` from `hext v` is passed to `hflow.flow`; only the later Ricci-trace identification uses local `contMDiffAt_extend'`. |
| `ScalarVariation.lean:19648` `eventually_timeDerivAt_eq_negTwoRicci_of_isClosedRicciFlowSolutionAt` | Neighborhood substitution theorem | Local/everywhere-near-`x` wrapper, but it delegates pointwise to the global-blocked theorem above. |
| `ScalarVariation.lean:19675` `TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near` | Algebraic substitution from eventual equality | Local; uses only the eventual equality produced by the previous theorem. |
| `ScalarVariation.lean:19746` `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near` | Laplacian substitution | Local; uses eventual equality and local congruence. |
| `ScalarVariation.lean:19825` `deltaGamma_koszul_negTwoRicci_of_isClosedRicciFlowSolutionAt_near` | First Koszul specialization | Local; obtains `hEq : ∀ᶠ y in nhds x, ...` and uses congruence at `x`. |
| `ScalarVariation.lean:19947` `covDeltaGamma_koszul_secondDerivAt_negTwoRicci_of_isClosedRicciFlowSolutionAt_near` | Differentiated Koszul specialization | Local; uses eventual equality and second-derivative congruence at `x`. |
| `ScalarVariation.lean:20371` `deltaRicciAt_eq_negTwoRicci_secondDerivContractionAt_of_isClosedRicciFlowSolutionAt_near` | Ricci variation substitution | Local; uses eventual equality and contraction congruence at `x`. |
| `ScalarVariation.lean:25063` `satisfiesRicciEvolutionAt_of_ricciFlow_curvatureCommutation` | Ricci evolution wrapper | Local downstream use; calls the previous substitution theorem. |
| `ScalarVariation.lean:25129` `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity` | Ricci evolution wrapper | Local downstream use; delegates to curvature-commutation wrapper. |
| `ScalarEvolution.lean:2877` `HamiltonScalarEvolutionPredicatesAt` | Predicate package | Stores the bundle; no proof use at definition site. |
| `ScalarEvolution.lean:2899` `HamiltonScalarEvolutionHessianPredicatesAt` | Predicate package | Stores the bundle; no proof use at definition site. |
| `ScalarEvolution.lean:2920` `HamiltonScalarEvolutionTraceDerivativePredicatesAt` | Predicate package | Stores the bundle; no proof use at definition site. |
| `ScalarEvolution.lean:2981` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation` | Direct scalar-evolution theorem consumer | Inherits the global blocker by calling `isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt` at `x`. |
| `ScalarEvolution.lean:3043` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail` | Neighborhood wrapper | Local downstream use, but it extracts `hext` at `x` and passes it to the direct scalar theorem above. |
| `ScalarEvolution.lean:3110` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` | Wrapper | Local downstream use; delegates to the algebraic-tail theorem. |
| `ScalarEvolution.lean:3188` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'` | Wrapper | Local downstream use; delegates to `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`. |
| `ScalarEvolution.lean:3348` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation` | Direct wrapper | Inherits the global blocker by delegating to the direct scalar theorem. |
| `ScalarEvolution.lean:3372` `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_trace_derivative_variation` | Direct wrapper | Inherits the global blocker by delegating to the Hessian wrapper. |
| `ScalarEvolution.lean:5001` `hamiltonScalarEvolutionProgram_of_predicates` | Program wrapper | Consumes predicate package and delegates to the direct scalar theorem, so it inherits the blocker. |
| `ScalarEvolution.lean:5023` `hamiltonScalarEvolutionProgram_of_hessianPredicates` | Program wrapper | Delegates through predicate conversion. |
| `ScalarEvolution.lean:5043` `hamiltonScalarEvolutionProgram_of_traceDerivativePredicates` | Program wrapper | Delegates through predicate conversion. |

## Why I did not apply the sanctioned weakening

The sanctioned weakening would make the bundle proveable from:

```lean
FiberBundle.contMDiffAt_extend' (k := 2) I E v
CovariantDerivative.derivRegularAt_extend (cov := g.leviCivita) (x := x) v
```

and would prove the intended static extension-regularity witness for the local
bundle.

However, that change alone does not repair the first consumer.  The proof still
needs to pass a global `CMDiff 2 (T% (extend E v))` proof to `hflow.flow`.
Making the local weakening typecheck would require one of these larger changes:

1. redefine the Ricci-flow solution predicate itself to test locally
   (`CMDiffAt` or an equivalent neighborhood form), or
2. prove a global smooth section/globally admissible replacement that agrees
   with `extend E v` near `x`, and use locality of `DerivRegularAt` and
   `ricciTraceAt`.

Neither is the requested mechanical hypothesis-shape change to
`ClosedRicciFlowExtensionRegularAt`.  The first changes the meaning of the
closed Ricci-flow interface; the second needs a globalization theorem not
present in the current API.

## Honest-strength update

The M4 downstream scalar/Ricci variation machinery is indeed local after it has
the pointwise equality

```lean
timeDerivAt gt t₀ y v w = -2 * (gt t₀).ricciAt y v w
```

eventually near the anchor.  The remaining obstruction is earlier: the current
definition of `IsClosedRicciFlowSolutionAt` exposes only a globally admissible
test-field equation.  Thus the extension-regularity gap is not confined to the
bundle definition; it is also in the flow-equation interface used by the first
bridge theorem.

No Lean definitions were changed.

## Verification

Command:

```bash
lake build Poincare.Global.MetricVariation Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, warnings only.
