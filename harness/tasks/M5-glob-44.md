Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-44: augmented dependence and the derivative package

Context: `harness/reports/M5-glob-43_blocked.md` (READ FIRST). PROVEN: the augmented field is `ContDiff ℝ 1` with the closed-ball `LipschitzOnWith` (`AugmentedC1.lean`); the second-variation PL package (`SecondVariation.lean`). THE REMAINING REPLAY: (2) GRÖNWALL DEPENDENCE of the augmented flow — two augmented solutions' difference under the Lipschitz bound (`GeodesicDependence.lean`'s pattern — its Grönwall core may be field-generic in `GronwallMembership/GeodesicDerivativeFinal.lean`'s abstract layers: CHECK and instantiate rather than replay); (3) the uniform remainders for the augmented field (`GeodesicDerivative.lean`'s compact-tube pattern — the field's `ContDiff 1` gives the Taylor estimates); (4) THE AUGMENTED FLOW DERIVATIVE: the residual argument (`SecondFlowDerivative.lean`'s theorem — its hypotheses are NOW SUPPLIABLE: the augmented ODE facts, the second-variation ODE (PL), the remainders from (3), the Lipschitz from `AugmentedC1`) ⟹ `HasFDerivAt (augmented flow) (second-variation endpoint) (hosted data)` — assemble into the NEIGHBORHOOD-LEVEL DERIVATIVE-FIELD PACKAGE `ExpChartC2` demands (the field = the second-variation endpoints; its C⁰/C¹ from the same estimates). FEED → `ExpChartC2 → ContDiffTwo → EndpointBridge → FTransitionDone` → 🎯 THE F-TRANSITION LAW. Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-glob-44_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/AugmentedDependence.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.AugmentedDependence` and report the actual result. Commit your work.
