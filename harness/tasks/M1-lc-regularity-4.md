Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-4: metric compatibility of the transported connection + bundle + identification

Context on main: read `harness/reports/M1-lc-regularity_blocked.md` (latest sections). Done so far: `chartTransportedLeviCivitaValueAt` API, uniqueness bridge (`..._eq_closed_of_isLeviCivitaAt`), `chartTransported_torsionFreeAt`, bracket/section intertwining (`chartTransportedLeviCivitaSection_mlieBracket_apply_chart`, `..._mdiffAt_apply_chart`), chartMetric isometry lemmas (`chartMetric_apply_chart`, `blendedChartMetric_eq_chartMetric_of_eq_one`). Remaining obstructions per the report:

1. **Metric compatibility**: prove `chartTransported_metricCompatibleAt` at arbitrary `y ∈ (extChartAt I x₀).source` (or on the sub-neighborhood where the blended metric equals chartMetric — restrict explicitly if needed). The missing tool named in the report: a fixed-chart scalar-derivative transport theorem — the derivative of a scalar function along the chart at y equals the model derivative of the pushed-forward function (generalize `chartTransportedLeviCivitaSection_mdiffAt_apply_chart`'s pattern from differentiability to the actual `extDerivFun`/`mfderiv` VALUE; ChartIdentification.lean has scalar chart lemmas — connect them).
2. **Bundling or bridge-generalization**: the uniqueness bridge takes the transported operator's pointwise LC properties. Either (a) bundle the transported values into an honest local `CovariantDerivative`-compatible object the bridge accepts, or (b) prove a variant of the bridge/`leviCivita_unique_at` that works with pointwise values only (check LeviCivitaUniqueness.lean's pointwise `leviCivita_unique_at` — it may already avoid the bundled operator; if so wire it directly).
3. **The prize**: combine 1 + 2 + `chartTransported_torsionFreeAt` into the unconditional local identification `chartTransportedLeviCivitaValueAt g x₀ σ y = closedLeviCivitaConnection g σ y` for differentiable σ, y in the (restricted) chart neighborhood.

Decompose aggressively, commit each green lemma, update the blocked-report with any remaining wall. No sorry/axiom. `lake build`, commit, report declaration names.
