Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-42: the anchored Gram/Ricci trace expansion → fire Bianchi bridges (1)/(2)

Read `harness/reports/M3-predicates-41_blocked.md` (exact remaining theorem surfaces). On main, NEW since the last attempt: `closedLeviCivitaConnection_contMDiff₂` (C² instance), canonical curvature-field differentiability, and the CANONICAL curvature entry bridge (no longer hypothesis-carried). The blocked item from M3-predicates-39 — the anchored Gram/Ricci trace step — now has every input:

Target: `∀ᶠ y in 𝓝 x, ClosedRicciDerivativeExpansionAt g y` (the frozen witness; consumers `eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt` + `eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt` fire immediately).

Route (all pieces on main):
1. Anchored Gram formula for the Ricci entries: `g.ricciAt y (ext u)(ext w) = Σ Gram⁻¹ · curvature-entries` near x (the `_eq_sum_gram_inv` pattern — `ricciAt_eq_curvature_contraction` gives the per-fiber trace; swap the fiber basis for the anchored gramFrameBasis exactly as `deltaGammaFirstSlotTraceFieldAt_eq_sum_gram_inv` did).
2. Differentiate: entry derivatives via the CANONICAL curvature entry bridge (on main, hypothesis-free for the canonical connection) + `gramMatrix_inv_extDerivFun_eq_neg_sum` + the Levi-Civita cancellation → `closedCovRicciDerivAt` shape.
3. Match the frozen witness statement exactly; ∀ᶠ via the ContMDiff vocabulary.
4. FIRE the consumers → **Bianchi bridges (1)/(2) DONE**. Report the sole remaining item: the cyclic core (bridge 3).

This is the 4th run of the identical Gram-expansion playbook (traceMetricVariation → deltaGamma first-slot → inner trace → now Ricci) — the proofs to mirror are all in the file. Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
