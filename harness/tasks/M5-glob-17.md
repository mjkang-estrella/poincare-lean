Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-17: instantiate hdiff — the concrete cutoff-one data

Context: `harness/reports/M5-glob-16_done.md` (READ FIRST — the abstract hdiff lemma + the exact instantiation spec it lists: `G0/G1 = chartGeodesicMetric`, `sigma = chartTransition`, `D = chartTransitionDeriv`, needing the cutoff-one pullback germ + local derivative hypotheses). PROVEN: the abstract hdiff (`PullbackDifferentiate.lean`), the pullback germ (`TransportedCompatibility.lean`), the algebraic consumer (`DifferentiatedCompat.lean`). THE INSTANTIATION: supply the derivative hypotheses — the chart metric is differentiable (`LocalConnectionRegularity/GeodesicChart.lean` regularity exports), the chart transition is smooth with derivative `chartTransitionDeriv` (the `extChartAt` transition smoothness — `ChartIdentification/ChartTransport.lean` or `contDiffOn_ext_coord_change`-shaped Mathlib API), the second derivative exists (same smoothness) — at points of the open cutoff-one zone. FEED: abstract hdiff → `DifferentiatedCompat`'s consumer → transported compatibility → (with the proven torsion-freeness) `LeviCivitaUniqueness.lean` → 🎯 THE TRANSITION LAW (the minus-sign identity, unconditional on the zone). Then the reanchor chain (`ReanchorLawFinal/ChristoffelTransition.lean`) fires. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-17_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/HdiffInstantiate.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.HdiffInstantiate` and report the actual result. Commit your work.
