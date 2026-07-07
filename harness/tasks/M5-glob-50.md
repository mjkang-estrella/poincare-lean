Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-50: the field is C¹ — the level-three discharge

Context: `harness/reports/M5-glob-49_done.md` (READ FIRST). PROVEN: the third-variation PL package (`ThirdVariation.lean`); the doubly-augmented field data (`FlowSmoothness.lean`'s ContDiff 2). THE REMAINING STAGES (the glob-31/32/44/45 patterns at level three): (1) the doubly-augmented uniform remainders (the field is ContDiff 1-with-modulus on tubes — the `AugmentedPackage.lean` Heine–Cantor pattern); (2) the doubly-augmented Grönwall dependence (`AugmentedDependence.lean` pattern — or the field-generic layer); (3) FEED the residual theorem (`SecondFlowDerivative.lean`'s abstract form — check genericity; else replay) at the doubly-augmented data ⟹ the second-variation-endpoint field (`sourceD`) has derivative facts + CONTINUITY of that derivative (the third-variation dependence estimates) ⟹ 🎯 `ContDiffAt ℝ 1 sourceD v` (and `targetD` identically — sphere side) — the EXACT demand of `ExpChartC2`. FEED → `FieldProducer`'s fields upgraded → `ExpChartC2 → ContDiffTwo → EndpointBridge → FTransitionDone` → 🎯🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-glob-50_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/FieldC1.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.FieldC1` and report the actual result. Commit your work.
