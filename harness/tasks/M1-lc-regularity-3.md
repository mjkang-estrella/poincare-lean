Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-3: transport preserves Levi-Civita (unconditional identification)

Context on main: `Poincare/Global/LeviCivitaTransport.lean` has the `chartTransportedLeviCivitaValueAt` API (transported connection value near x₀, with source/target/roundtrip lemmas) and the uniqueness bridge `chartTransportedLeviCivitaValueAt_eq_closed_of_isLeviCivitaAt`: IF the transported candidate is torsion-free and metric-compatible at y THEN it equals `closedLeviCivitaConnection g` at y. Read `harness/reports/M1-lc-regularity_blocked.md` (updated section) for the precise remaining obstruction.

Deliverable: discharge the IF — prove the transported operator is Levi-Civita:

1. `chartTransported_torsionFreeAt`: torsion-freeness of the transported operator at y near x₀. Route: the model `chartLeviCivita` is torsion-free; transport preserves torsion because the chart tangent maps intertwine Lie brackets (the blocked-report points to `ChartIdentification.lean`'s scalar and bracket chart lemmas — connect them to the `chartTransportedLeviCivitaValueAt` API; prove any missing intertwining lemma as its own commit).
2. `chartTransported_metricCompatibleAt`: metric compatibility at y — `chartMetric` was built as the isometric pullback, so compatibility of the model connection with `chartMetric` transports to compatibility of the transported operator with `g.inner`. Again via the chart-derivative intertwining.
3. Combine with the existing bridge: `chartTransportedLeviCivitaValueAt_eq_closed (y near x₀, σ differentiable) : chartTransportedLeviCivitaValueAt ... = closedLeviCivitaConnection g σ y` — unconditional.
4. Mind the blocked-report's note about the neighborhood where the blended metric equals chartMetric — restrict all statements to that neighborhood explicitly; a neighborhood-restricted identification is fully acceptable (gluing is the next task).

This is the hardest remaining piece of the regularity chain. Decompose aggressively; commit every green lemma; update the blocked-report honestly if a wall remains. No sorry/axiom. `lake build`, commit, report declaration names.
