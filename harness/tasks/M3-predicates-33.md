Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-33: ClosedContractedBianchiAt — THE LAST PREDICATE

The Hamilton scalar-evolution theorem on closed manifolds stands modulo regularity classes + ONE predicate: `ClosedContractedBianchiAt (gt t₀) x` (read its exact frozen statement — the twice-contracted second Bianchi: div Ric = ½ dR, in whatever closed shape it was frozen in ScalarVariation/ScalarEvolution.lean).

Survey FIRST (30 min budget), then attack:
1. **Existing assets**: `Poincare/BianchiIdentity.lean` (manifold-level FIRST Bianchi, GENUINE per the audit), `CurvatureTensoriality.lean` (curvatureOp, ricciBilinearAt machinery), and the model's `coord_twice_contracted_bianchi` (~ModelLaplacian 6767) + `einstein_tensor_divergence_free_of_contDiff` / `fderiv_coordScalar_eq_two_ricciDivergenceForm_of_contDiff` (the model's SELF-CONTAINED contracted Bianchi from G C³ — the audit's consolidation thread). Also `ricciAt_symm` and the whole Gram/extend derivative toolkit built these two days.
2. **Route decision**: (A) native closed proof — differentiate the closed curvature via the extend/Gram machinery and replay the model's contracted-Bianchi computation (the model proof is the template; heavy but the toolkit now exists — the SAME pattern as the keystone campaign); (B) second-Bianchi via `covDeltaGamma_koszul`-style differentiation of the curvature's Koszul expression; (C) if the closed statement can be phrased through the canonical connection's chart transport, transport the model theorem (the goal-1 identification machinery — but recall transport routes have historically stalled; prefer A).
3. Decompose aggressively (the keystone campaign averaged ~5 lemmas/task); commit each green lemma; if the full predicate needs multiple sessions, land the decomposition + first lemmas + exact-goal report — the next task continues.
4. If it CLOSES: state the FINAL consolidated theorem `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` (honest regularity classes ONLY) + `hamiltonScalarEvolutionProgram_...` final form. Update notes + HARNESS_STATUS-worthy summary in the done report.

Standing sanity-check rule (static/torus/round-sphere informal). Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
