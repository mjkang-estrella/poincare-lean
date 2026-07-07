Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-41: ContDiffAt 2 F — the augmented flow's C¹, non-circular

Context: `harness/reports/M5-glob-40_blocked.md` (READ FIRST). THE ONE PRODUCER: `ContDiffAt ℝ 2 F (eM v)` at the ball points — everything else feeds `EndpointBridge → FTransitionDone` → the law. ⚠️ NON-CIRCULARITY: do NOT derive it from the DF chain (which consumes it); derive DIRECTLY: (1) THE AUGMENTED FLOW'S C¹: the augmented system (geodesic + first variation — `SecondVariation.lean`) has its PL package; the FIRST-order smooth-dependence chain (`GeodesicDependence/GeodesicDerivative/GeodesicDerivativeFinal/GeodesicFlowDerivative.lean`) — CHECK whether its statements are field-generic or chartChristoffel-specific; if specific, REPLAY the chain at the augmented field (the proofs are structural — Lipschitz + Grönwall + residuals; the augmented field is smooth with bounded derivatives on the tube); the augmented flow C¹ in initial data = F's flow part C²; (2) `ContDiffAt 2` ASSEMBLY: Mathlib's `contDiffAt_succ_iff_hasFDerivAt` — F has a derivative field on a neighborhood (the flow derivative, C¹ by (1)) that is `ContDiffAt 1` ⟹ `ContDiffAt 2 F`; the chart compositions preserve it (exp charts C² by the same flow facts; L linear). FEED → `EndpointBridge` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-41_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ContDiffTwo.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ContDiffTwo` and report the actual result. Commit your work.
