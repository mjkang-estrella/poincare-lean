Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-5: open the Ricci-identity commutation campaign (roadmap subtask 1, first slice)

The Ricci-evolution target is fully trace-validated on main. The sole remaining content: convert `deltaRicciSecondDerivContractionAt (negTwoRicciVariationField g)` (the flow-specialized δRic in second-derivative form — read the M4-prep-1 groundwork in ScalarVariation.lean ~13007) into the `lichnerowiczLaplacianAt + ricciQuadraticAt` vocabulary. This is the tensor-level analogue of the scalar keystone (which took ~15 tasks) — this task is the OPENING SLICE only:

1. **Survey + plan** (write to the report first): read the model's corresponding chain (`ricciDeriv` → Lichnerowicz in ModelLaplacian — the `g_covDeltaGammaDeriv_lichnerowicz` route and the Uhlenbeck-free 3D shortcuts if any) and map which closed assets carry over (covDeltaGamma_koszul, the ∇²h machinery — with h = −2Ric the ∇²Ric objects, the cyclic second Bianchi JUST PROVEN, the Ricci identity/curvature commutation from CurvatureTensoriality). Produce the slice plan (≤6 slices, exact Lean statements).
2. **First slice**: the substitution h = −2Ric into `covDeltaGamma_koszul` → ∇δΓ for the flow in ∇²Ric 3-term form (the flow-specialized covariant Koszul — mostly rewiring, the linearity lemmas exist).
3. **Second slice if budget**: the commutation entry — where the second Bianchi (on main, proven!) enters: the div-of-∇Ric reorderings that produce the curvature quadratics (the model route shows which contraction; the twice-contracted Bianchi consequences `div Ric = ½dR` forms are on main via ClosedContractedBianchiAt-canonical).

Standing sanity checks (trace each new identity against the validated scalar shapes where applicable). Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
