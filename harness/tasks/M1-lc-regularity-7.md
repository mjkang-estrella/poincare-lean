Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity-7: execute the 7-step localization plan → THE GOAL INSTANCE

Read `harness/reports/M1-lc-regularity-6_blocked.md` in full. It contains an explicit 7-step plan for the LAST remaining gap: localized chart-side hom-section smoothness, then the goal. All bridges are on main and gate-verified:
- hom helper + coordinate normalization: `chartTransportedLeviCivitaHom`, `..._apply`, `..._inCoordinates_apply_chart` (Global/LeviCivitaRegularity.lean)
- the EventuallyEq bridge: `chartTransportedLeviCivitaHom_eventuallyEq_closed`
- chart-side applied smoothness: `chartTransportedLeviCivitaSection_contMDiffAt_apply_chart`
- model regularity any order: `leviCivitaConnection_contMDiff` (ModelChristoffel.lean)
- `LocalConnectionRegularity.lean` — the bump/globalization pattern the report names for step 3 (`ContMDiffOn.smul_section_of_tsupport` etc.)

Execute the plan's steps (bump-localize the transported section, apply `chartLeviCivita_contMDiff` to the localized section, transfer regularity back by covariant-derivative germ locality, compose through `extChartAt` + the inCoordinates lemma, fire `ContMDiffAt.congr_of_eventuallyEq`, generalize over x₀), committing each verified step, and conclude:

```
theorem/instance closedLeviCivitaConnection_contMDiff
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivitaExistence.closedLeviCivitaConnection g) 1
```

Then the demonstration corollary: `ricciAt_symm'` (any Curvature.lean theorem restated with NO carried regularity hypothesis — the instance supplies it).

If a step genuinely fails, commit greens + refine the report with the exact failing subgoal. No sorry/axiom. `lake build`, commit, report declaration names.
