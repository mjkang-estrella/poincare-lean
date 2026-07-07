Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-51: the C¹ assembly — the tower closes

Context: `harness/reports/M5-glob-50_blocked.md` (READ FIRST). PROVEN AT LEVEL THREE: the PL package (`ThirdVariation.lean`), the compact-uniform remainders (`FieldC1.lean`), the field data (`FlowSmoothness.lean`). THE CLOSING STAGES: (1) the doubly-augmented Grönwall dependence (the `AugmentedDependence.lean` pattern — the field-generic Grönwall core instantiated); (2) FEED the residual theorem (`SecondFlowDerivative.lean`'s form at the doubly-augmented data — the hypotheses now all exist) ⟹ the doubly-augmented flow derivative ⟹ the second-variation-endpoint field has a derivative (the third-variation endpoint) at each hosted point; (3) CONTINUITY of that derivative (the third-variation dependence — from (1)); (4) 🎯 `ContDiffAt ℝ 1 sourceD v` + `targetD` (the C¹ characterization: differentiable with continuous derivative — `contDiffAt_one_iff`-shaped assembly). FEED → `FieldProducer → ExpChartC2 → ContDiffTwo → EndpointBridge → FTransitionDone` → 🎯🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-51_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TowerCloses.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TowerCloses` and report the actual result. Commit your work.
