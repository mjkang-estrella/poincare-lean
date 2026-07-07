Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-45: remainders and the package — the augmented derivative lands

Context: `harness/reports/M5-glob-44_blocked.md` (READ FIRST). PROVEN: the augmented field C¹+Lipschitz (`AugmentedC1.lean`); the augmented Grönwall dependence (`AugmentedDependence.lean`); the residual theorem awaiting its inputs (`SecondFlowDerivative.lean`); the second-variation PL solutions (`SecondVariation.lean`). THE REMAINING STAGES: (3) THE UNIFORM REMAINDERS for the augmented field — the field is `ContDiff 1` on the tube; the compact-tube Taylor estimates (`GeodesicDerivative.lean`'s pattern — its uniform-remainder lemmas: check field-genericity; the `ContDiff 1` modulus of continuity of the derivative on the compact tube gives the uniform `o(‖δ‖)` — Heine–Cantor); (4) FEED `SecondFlowDerivative`'s theorem (its hypothesis list: the augmented ODE facts ✓ (`SecondDischarge`), the second-variation ODE ✓ (PL), the remainders (3), the Lipschitz ✓) ⟹ the augmented flow derivative at the hosted data; ASSEMBLE the NEIGHBORHOOD DERIVATIVE-FIELD PACKAGE (`ExpChartC2.lean`'s demanded shape — the field of second-variation endpoints with its `HasFDerivAt` facts + continuity from the dependence estimates). FEED → `ExpChartC2 → ContDiffTwo → EndpointBridge → FTransitionDone` → 🎯 THE F-TRANSITION LAW. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-45_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/AugmentedPackage.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.AugmentedPackage` and report the actual result. Commit your work.
