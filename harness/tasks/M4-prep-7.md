Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-7: commutation slices 4-5 (the curvature commutation core)

Read `harness/reports/M4-prep-5_done.md` — slices 1-3 are on main. Execute slices 4 and 5 per the plan's exact numbered Lean statements (each its own commit):

- Slice 4 (per the plan): the statement it authors at position 4 — read it verbatim from the report and prove exactly that (from memory of the plan tail: the Ricci-identity/curvature-commutation predicate discharge or the divergence-reordering block feeding `RicciSecondDerivCommutationAt`).
- Slice 5 (per the plan): the `RicciSecondDerivCommutationAt (gt t₀) x` discharge or its immediate predecessor per the plan's numbering.

Tools on main (the plan's own inventory): the closed Ricci identity machinery (`CurvatureTensoriality`, `closedCurvature_koszul`, `curvatureOp_antisymm`), the proven cyclic second Bianchi + `ClosedContractedBianchiAt`-canonical consequences, the discharged trace-commutes, the full Gram/Hessian second-derivative toolkit, and the slice-2/3 specializations just merged.

Standing correction protocol if an authored statement fails sanity (refute exactly + propose fix). Trace-check landed identities. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
