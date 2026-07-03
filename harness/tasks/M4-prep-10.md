Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-10: the two tensor-slot bridges → close the tensor Ricci identity

Read `harness/reports/M4-prep-9_blocked.md` — its "Next slice" plan is this task (each item its own commit):

1. Closed analogues of the model's `fderiv_tensor_corr_field`/`fderiv_tensor_corr_field'` for `CovTensor2ExtContMDiffAt h x 2` — the uncontracted product-rule bridges for a raw (0,2) tensor field in moving canonical-extension slots, stated in `extDerivFun` form (the entry-bridge proof pattern from `DeltaGammaEntryDerivativeBridgeAt` / `closedCurvatureEntryDerivativeBridgeAt` — the SAME triple product rule, now for a generic h).
2. The closed `christoffel_antisymm_deriv_eq_curvature` analogue: the antisymmetrized derivative of the slot connection field = `CovariantDerivative.curvatureOp` — via the `closedCurvature_koszul`/connection-entry expansion stack (on main; this is essentially re-reading `closedCurvature_koszul` as the antisymmetrization identity — may be a short rearrangement).
3. Combine with `covTensor2SecondDerivAt_antisymm_expansion` + `covTensor2SecondDerivAt_pure_schwarz_cancel` (on main) → **the closed tensor Ricci identity**: antisymmetrized `covTensor2SecondDerivAt` = `covTensor2SecondDerivCurvatureActionAt`.
4. Specialize to `ricciVariationField g` (discharge-plan slice 2).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
