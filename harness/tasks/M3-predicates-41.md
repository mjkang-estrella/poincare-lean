Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-41: upgrade the closed Levi-Civita regularity to order 2

SCOPE: one upgrade. Read `harness/reports/M3-predicates-40_blocked.md`. The curvature-field differentiability witness needs the canonical connection at ORDER 2; the goal-1 chain proved `closedLeviCivitaConnection_contMDiff` at order 1 only — but its ingredients are order-generic:
- `CovariantDerivative.leviCivitaConnection_contMDiff` (ModelChristoffel.lean) — ANY order k.
- `chartLeviCivita_contMDiff` (ChartTransport.lean) — check its order parameter.
- The transport identification + hom-bundle EventuallyEq (order-independent equalities).
- The final gluing (`chartTransportedLeviCivitaHom_contMDiffAt` + `closedLeviCivitaConnection_contMDiff`, Global/LeviCivitaRegularity.lean) — pinned at 1.

Deliverables:
1. Generalize the gluing chain to order k (or just k = 2 if generic is awkward): `closedLeviCivitaConnection_contMDiff₂ : ContMDiffCovariantDerivative (closedLeviCivitaConnection g) 2` (and the `g.leviCivita` wrapper). The proof should be the goal-1 proof with the order bumped — the metric is ∞-smooth so every smoothness input upgrades for free; chase the order parameters through the localized covariant-derivative regularity lemma named in the report.
2. Derive the curvature-field differentiability witness (`CurvatureFieldMDifferentiableAt`-style, per predicates-40's bridge hypothesis) for the canonical connection from the order-2 instance.
3. Chain: the bridge (on main) fires → `ClosedRicciDerivativeExpansionAt` near x (the anchored Gram/Ricci trace step per M3-predicates-39_blocked.md — the standard cancellation) → the predicates-38 consumers → **Bianchi bridges (1)/(2) DONE**. Note bridge (3) (cyclic core) as the sole remaining item.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.LeviCivitaRegularity Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
