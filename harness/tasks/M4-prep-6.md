Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-6: commutation slices 2-3 (per the M4-prep-5 plan)

Read `harness/reports/M4-prep-5_done.md` — the 6-slice plan, slice 1 done (`covDeltaGamma_koszul_secondDerivAt_negTwoRicci_of_isClosedRicciFlowSolutionAt_near` on main). Execute slices 2 and 3 per the plan's exact statements (each its own commit; consult the plan file for the precise Lean shapes — they were authored by the previous worker with the current API in view):

- Slice 2: the second-derivative contraction reorganization (the div/trace reorderings of ∇²Ric that expose the rough Laplacian block — the `deltaRicciSecondDerivContractionAt` decomposition; the second-order Gram/Hessian machinery and the discharged trace-commutes are the tools).
- Slice 3: the curvature-commutation entry — where reordering covariant derivatives produces the Riemann-action terms (the closed Ricci identity: `covTensor2SecondDerivAt` antisymmetrized = curvature action; check `CurvatureTensoriality`/`RiemannCurvatureOperator` for the manifold-level Ricci identity and the `closedCurvature_koszul` machinery on main; the cyclic second Bianchi provides the divergence-side reorderings).

If a slice's statement (authored in the plan) fails a sanity check, apply the standing correction protocol (refute exactly, propose the fix). Trace each landed identity against the validated scalar shapes. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
