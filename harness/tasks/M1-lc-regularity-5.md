Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-5: THE GOAL — global regularity instance via local regularity + gluing

This is the final step of the regularity chain. Context on main (read `harness/reports/M1-lc-regularity_blocked.md` fully):
- Model-space regularity: `CovariantDerivative.leviCivitaConnection_contMDiff` (ModelChristoffel.lean, any order).
- Local identification: `Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` — near any x₀ (on the cutoff-one neighborhood), `closedLeviCivitaConnection g` agrees with the chart-transported model connection.
- `chartLeviCivita_contMDiff` (ChartTransport.lean) — model-side smoothness.
- Definition of the target class: `CovariantDerivative.ContMDiffCovariantDerivative` (Mathlib, VectorBundle/CovariantDerivative/Basic.lean) — read exactly what it requires (likely: for ContMDiff sections σ and smooth directions, the output section y ↦ cov σ y v(y) is ContMDiff, or a ContMDiffOn/local formulation).

Deliverable — the goal theorem, in `Poincare/Global/LeviCivitaRegularity.lean` (+ root import):

```
theorem/instance closedLeviCivitaConnection_contMDiff
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivitaExistence.closedLeviCivitaConnection g) 1
```

Route: smoothness is local, so for each x₀ pick the cutoff-one neighborhood; on it the connection value IS the transported model value (identification); the transported value is a composition of: chart tangent maps (smooth), the model Levi-Civita of the (blended) chart metric (ContMDiff by `leviCivitaConnection_contMDiff`/`chartLeviCivita_contMDiff`), and inverse chart maps (smooth on source). Compose (`ContMDiffAt.comp`, `contMDiffOn_of_locally_contMDiffOn`, `contMDiffAt_iff_contMDiffOn_nhds`-style lemmas) to get `ContMDiffAt` at x₀; conclude globally since x₀ arbitrary.

Watch out: the identification requires σ differentiable and holds for VALUES; the ContMDiff class quantifies over sections — make sure the local rewrite is done as a `Filter.EventuallyEq` (the connection outputs agree on a neighborhood) so `ContMDiffAt.congr_of_eventuallyEq` applies.

If the full instance stalls, the fallback deliverable is `ContMDiffAt`-at-every-point for each fixed smooth section (a named theorem), plus the precise remaining gap in the report. But push hard for the instance: order 1 suffices.

After the instance: add a demonstration — restate ONE Curvature.lean theorem (e.g. `ricciAt_symm`) as a corollary with NO carried regularity hypothesis (the instance now supplies it). Name it `ricciAt_symm'` or similar.

No sorry/axiom. `lake build`, commit each piece, report declaration names.
