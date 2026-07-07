Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-46: feed the residual theorem — the neighborhood package lands

Context: `harness/reports/M5-glob-45_blocked.md` (READ FIRST). ALL HYPOTHESES OF `SecondFlowDerivative.augmentedFlow_hasDerivAt_of_secondVariation_gronwall` NOW EXIST: the augmented ODE facts (`SecondDischarge.lean`), the second-variation ODE (`SecondVariation.lean`'s PL solutions), the compact-convex uniform remainders (`AugmentedPackage.lean`), the Lipschitz tube control (`AugmentedC1/AugmentedDependence.lean`). FEED THEM: (1) instantiate the residual theorem at the hosted data ⟹ the augmented flow derivative (`HasDerivAt/HasFDerivAt`-shaped in the initial data, with the second-variation endpoint); (2) ASSEMBLE the NEIGHBORHOOD DERIVATIVE-FIELD PACKAGE (`ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields`'s exact demanded fields — READ them: the derivative field on a neighborhood + its `HasFDerivAt` facts + continuity; the field = the flow-derivative/second-variation endpoints; continuity from the dependence estimates); (3) BOTH SIDES (the sphere identically). FEED → `ExpChartC2 → ContDiffTwo → EndpointBridge → FTransitionDone` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-46_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/PackageLands.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.PackageLands` and report the actual result. Commit your work.
