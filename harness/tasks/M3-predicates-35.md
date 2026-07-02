Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-35: the Bianchi bridge lemmas (with a pivot checkpoint)

Read `harness/reports/M3-predicates-34_blocked.md` — it lists 4 bridge lemmas transporting the MODEL's generic contracted Bianchi (`fderiv_coordScalar_eq_two_ricciDivergenceForm_of_contDiff`, proven for ANY C³ metric on model space, hence for the chart representative Ghat) to `ClosedContractedBianchiOneFormAt`.

PIVOT CHECKPOINT (do this FIRST, ≤1 hour of exploration): the historical failure mode of transport routes in this project was raw-frame/section differentiability pathology (see memory of predicates-9..11). Bianchi may dodge it because curvature is TENSORIAL. Verify quickly: state bridge lemma 3 (`tensorDivergenceOneFormAt g (ricci-field) at chart point = model ricciDivergence of Ghat`) and check whether the two sides' DEFINITIONS unfold to comparable chart expressions (the closed curvature via `g.leviCivita` = transported model connection near x₀ — the goal-1 identification `chartTransportedLeviCivitaValueAt_eq_closed...` is exactly the connection-level bridge!). If the unfolding looks tractable → proceed with the 4 bridges. If the raw-frame pathology reappears → PIVOT to the native route: replay the model's `coord_second_bianchi` computation in the extend frame (the predicates-26-31 toolkit), and record the pivot decision.

Deliverables (each its own commit):
1. Bridge lemma 1: chart representative Ghat is C³ (from g's smoothness via chartMetric machinery — `contDiff_chartMetric_iff` in ChartTransport.lean).
2. Bridge lemma 2 (connection identification near the chart point): closed `g.leviCivita` values = model Levi-Civita of Ghat — reuse the goal-1 transport identification (`chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` + the eventuallyEq hom machinery).
3. Bridge lemma 3 (Ricci-divergence) and 4 (exterior derivative) per the report's exact statements — curvature/Ricci are compositions of connection values, so lemma 2 + the derivative bridges should chain.
4. If all bridges land: discharge `ClosedContractedBianchiOneFormAt` via the model theorem → `of_oneForm_near` fires → **`ClosedContractedBianchiAt` DISCHARGED** → the FINAL Hamilton theorem (regularity classes only) — state it + done-report.

Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
