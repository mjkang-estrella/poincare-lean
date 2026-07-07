Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-16: hdiff — differentiate the pullback germ

Context: `harness/reports/M5-glob-15_blocked.md` (READ FIRST — the VERBATIM `hdiff`). PROVEN: the pullback law on the cutoff-one zone (`TransportedCompatibility.lean` — an EQUALITY of functions on a zone/germ) + the algebraic step consuming `hdiff` (`DifferentiatedCompat.lean`). THE DERIVATION: differentiate the pullback identity — an equality of smooth functions on an OPEN set differentiates term by term (`Filter.EventuallyEq.fderiv_eq` on the neighborhood, or `fderiv_congr` on the open zone — the zone is open per the cutoff-one construction); the LHS derivative expands by the product/composition rules (the chart metric is smooth — `LocalConnectionRegularity/GeodesicChart.lean` regularity; `σ` is smooth — the chart transition; `HasFDerivAt` product/comp lemmas); MATCH the resulting expression to `hdiff`'s exact shape (the D²σ terms from differentiating Dσ — `ContDiff` second-derivative API). Feed `DifferentiatedCompat` → the transported compatibility → LC uniqueness (`LeviCivitaUniqueness.lean`) → THE TRANSITION LAW → the reanchor chain fires. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-16_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/PullbackDifferentiate.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.PullbackDifferentiate` and report the actual result. Commit your work.
