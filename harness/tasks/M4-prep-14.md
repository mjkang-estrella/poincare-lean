Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-14: trace the tensor Ricci identity → RicciSecondDerivCurvatureCommutationAt → THE RICCI EVOLUTION EQUATION

Read `harness/reports/M4-prep-8_done.md` (plan items 3-5) and the M4-prep-13 landing. On main: the closed tensor Ricci identity + its `ricciVariationField` specialization, `RicciSecondDerivCurvatureCommutationAt` (the frozen predicate exposing rough − 2Rm + Ric-action + quadratic), the `of_closed_bianchi` bridge, and `satisfiesRicciEvolutionAt_of_secondDerivCommutation` (the assembly, waiting).

Deliverables (each its own commit):
1. **Trace the identity** (plan item 3): contract the Ricci-field tensor Ricci identity over the basis/sharp pairings appearing in `deltaRicciSecondDerivContractionAt`; isolate the rough Laplacian, Lichnerowicz curvature action, Ricci-endomorphism action, and `ricciQuadraticAt` blocks (the trace machinery: the discharged trace-commutes, `sum_metricDualVectorAt_contraction_swap`, the trace-validated vocabulary identities from M4-prep-3/4).
2. **Package** (plan item 4): the traced result = `RicciSecondDerivCurvatureCommutationAt g x` — DISCHARGED (with honest regularity hypotheses; the canonical instances should supply most).
3. **Fire the chain** (plan item 5): `of_closed_bianchi` (its cyclic-Bianchi hypothesis is PROVEN on main — `eventually_closed_cyclic_second_bianchi`) → `RicciSecondDerivCommutationAt` → `satisfiesRicciEvolutionAt_of_secondDerivCommutation` + the flow δRic HasDerivAt (the deltaRicci chain on main) → **`satisfiesRicciEvolutionAt_of_ricciFlow`: THE RICCI TENSOR EVOLUTION EQUATION** under honest classes. Historic done-report.

This is the tensor campaign's final assembly. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
