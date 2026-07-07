Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-14: transported compatibility — the pullback metric law

Context: `harness/reports/M5-glob-13_blocked.md` (READ FIRST — the three remaining pieces VERBATIM: metric-compatibility packaging, inverse target-coordinate packaging, velocity chain-rule producer). PROVEN: transported torsion-freeness (`TransitionLaw.lean`). THIS TASK: (1) THE METRIC TRANSITION LAW: the target blended chart metric is the σ-pullback of the source one — `G¹(σx)(Dσ u, Dσ w) = G⁰(x)(u, w)` — from the DEFINITIONS (`CovariantDerivative.chartMetric` unfolds to `g.inner` at the point through the charts — the two chart expressions read the SAME `g.inner`; chart-composition algebra — READ the definition and prove); (2) TRANSPORTED COMPATIBILITY: differentiate (1) along a direction, apply the source compatibility identity (`chartChristoffelField_pairing_eq_blendedChartMetric`-shaped, `GeodesicSpeed.lean`), the chain rule turns the source Γ-terms into the transported-Γ terms + the D²σ corrections matching the minus-sign law — conclude the transported field satisfies the TARGET compatibility identity; (3) if room: the inverse-coordinate packaging (σ is the chart transition — a `PartialHomeomorph` composition with smooth inverse — the `extChartAt` transition machinery). Strict-partial per piece; ONE isolated statement max. Report `harness/reports/M5-glob-14_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TransportedCompatibility.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TransportedCompatibility` and report the actual result. Commit your work.
