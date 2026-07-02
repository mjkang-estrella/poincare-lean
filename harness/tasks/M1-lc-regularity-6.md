Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-6: the hom-bundle EventuallyEq bridge → THE GOAL INSTANCE

Read `harness/reports/M1-lc-regularity-5_blocked.md` in full — it isolates the ONE remaining obstruction for the goal, and all supporting lemmas are already on main:
- `CovariantDerivative.chartTransportedLeviCivitaSection_contMDiffAt_apply_chart` (Global/LeviCivitaRegularity.lean) — chart-side smoothness.
- `chartLeviCivita_contMDiff` (ChartTransport.lean).
- `Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` — value identification on the cutoff-one neighborhood.
- `CovariantDerivative.leviCivitaConnection_contMDiff` (ModelChristoffel.lean) — model regularity at any order.

Remaining work (per the report):
1. **Hom-bundle EventuallyEq**: for fixed smooth σ and each x₀, on the cutoff-one neighborhood, prove the total-space hom section `fun y => TotalSpace.mk' _ y ((closedLeviCivitaConnection g) σ y)` is `Filter.EventuallyEq` near x₀ to the chart-pushed smooth chart-side hom section. The content: upgrade the pointwise applied equality (`... σ hy v = closed ... σ y v` for every tangent v) to equality of the dependent continuous linear maps — `ContinuousLinearMap.ext` fiberwise gives CLM equality at each y in the neighborhood; the work is managing the tangent-bundle trivializations/`TotalSpace.mk'` coordinates so both sides live in the same fiber representation. Search Mathlib for the hom-bundle/`Bundle.ContinuousLinearMap` chart lemmas (`Trivialization.continuousLinearMap`, `hom_trivializationAt_apply`, `inCoordinates` — Mathlib's `ContMDiffAt` for bundle-hom sections is usually phrased via `inCoordinates`; working through `inCoordinates` may let you avoid explicit TotalSpace equality entirely).
2. **Fire the gluing**: `ContMDiffAt.congr_of_eventuallyEq` + the pieces above → `ContMDiffAt` of the connection-applied section at x₀ → x₀ arbitrary → the class's `contMDiff` field → the GOAL:
   `theorem/instance closedLeviCivitaConnection_contMDiff (g) : CovariantDerivative.ContMDiffCovariantDerivative (LeviCivitaExistence.closedLeviCivitaConnection g) 1`.
3. **Demonstration**: `ricciAt_symm'` (or any Curvature.lean theorem) as a corollary with no carried regularity hypothesis.

If the `inCoordinates` route stalls too, commit greens and write the refined report — but this gap is narrow; expect it to close. No sorry/axiom. `lake build`, commit each piece, report declaration names.
