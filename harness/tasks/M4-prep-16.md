Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-16: the curvature-action trace fold → THE RICCI EVOLUTION EQUATION FIRES

Read `harness/reports/M4-prep-15_blocked.md` — it displays the EXACT remaining fold:
`Σᵢ CA(bᵢ, u, w, ♯bⁱ) + Σᵢ CA(bᵢ, w, u, ♯bⁱ) = 2·lichnerowiczCurvatureAt − ricciActionOnTensorAt − ricciQuadraticAt` (with CA = `covTensor2SecondDerivCurvatureActionAt` on the Ricci field).

This is pure fiberwise curvature algebra: unfold `covTensor2SecondDerivCurvatureActionAt`'s definition (the curvature action on the 2-tensor: two slot-action terms per the tensor Ricci identity's RHS), expand the curvature contractions in the basis, and match against the definitions of `lichnerowiczCurvatureAt` (the corrected mixed contraction — trace-validated!), `ricciActionOnTensorAt`, `ricciQuadraticAt` (with `ricciVariationField = Ric` the quadratic terms appear via `ricciAt_eq_curvature_contraction`). Tools: curvature symmetries (`curvatureOp_antisymm`, first Bianchi from BianchiIdentity.lean, `ricciAt_symm`), the swap machinery, `ring`.

Sanity-check the fold on the constant-curvature pattern FIRST (standing rule — the M4-prep-2 episode showed these folds are where sign/slot errors hide; if the fold is FALSE as displayed, refute exactly and identify which definition's convention mismatches).

Then: the fold → the M4-prep-15 assembly completes → `RicciSecondDerivCurvatureCommutationAt` DISCHARGED → `satisfiesRicciEvolutionAt_of_ricciFlow_curvatureCommutation` fires → **THE RICCI TENSOR EVOLUTION EQUATION** (∂ₜRic = Lichnerowicz + quadratics under the flow, honest classes). Historic done-report + updated notes with the M4 pinching outlook.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
