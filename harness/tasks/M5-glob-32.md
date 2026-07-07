Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-32: discharge at the geodesic data — F is C²

Context: `harness/reports/M5-glob-31_done.md` (READ FIRST — the theorem's hypothesis list). PROVEN: `augmentedFlow_hasDerivAt_of_secondVariation_gronwall` (`SecondFlowDerivative.lean`). THE DISCHARGE (mirror the first-order instantiation — `GeodesicFlowDerivative.lean`'s proof discharged the analogous hypotheses at the geodesic data): (1) the augmented ODE facts — the geodesic + first-variation pair solves the augmented system (the existing flow + linearized facts combined — `GeodesicLinearized/LinearizedFamilyExport.lean`); (2) the second-variation ODE — glob-30's PL package solutions; (3) the compact Taylor remainders for the AUGMENTED field — the field is built from Γ and DΓ (smooth — `LocalConnectionRegularity.lean`); the remainder machinery (`GeodesicDerivative.lean`'s compact-tube uniform remainders) applies to the augmented field the same way; (4) Lipschitz tube control — same. INSTANTIATE → the fixed-time augmented derivative at the geodesic data → 🎯 `fderiv F` DIFFERENTIABLE (the exp chart's second-order regularity — the augmented derivative's first component IS the derivative of the flow derivative; convert to the `D`-field differentiability demanded by `GermAndField/FTransition.lean`). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-32_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/SecondDischarge.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.SecondDischarge` and report the actual result. Commit your work.
