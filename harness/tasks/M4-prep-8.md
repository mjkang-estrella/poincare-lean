Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-8: slice 6 assembly + open the curvature-commutation discharge

Read `harness/reports/M4-prep-7_done.md` and `M4-prep-5_done.md`. On main: slices 1-5 (the flow-specialized Koszul, the −2Ric specializations, `RicciSecondDerivCommutationAt` + `RicciSecondDerivCurvatureCommutationAt` + the `of_closed_bianchi` bridge). Two deliverables:

1. **Slice 6 — assembly**: `satisfiesRicciEvolutionAt_of_secondDerivCommutation` per the plan's exact statement (M4-prep-5 report, item 6): from the flow δRic HasDerivAt hypothesis + `RicciSecondDerivCommutationAt`, conclude `SatisfiesRicciEvolutionAt gt t₀ x`. The pieces: `deltaRicciAt_eq_secondDerivContractionAt`-chain (slices 1-3) + the commutation predicate + HasDerivAt congruence. THE RICCI EVOLUTION EQUATION, modulo the commutation predicate — the tensor analogue of where the Hamilton campaign stood after variation-9.
2. **Open the discharge of `RicciSecondDerivCurvatureCommutationAt`** (the real remaining math — the tensor Ricci identity computation): survey what the closed Ricci-identity assets give (`curvatureOp` antisymmetry, `closedCurvature_koszul`, the `covTensor2SecondDerivAt` antisymmetrization = curvature action — is there a proven closed lemma of that shape? CurvatureTensoriality/RiemannCurvatureOperator have the operator-level versions); land the first honest slice (e.g. the antisymmetrized-∇² = curvature-action identity for the Ricci field entries, via the closedCurvature_koszul technology) + a slice plan for the rest.

Standing protocols (sanity, correction, exact-goal). No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
