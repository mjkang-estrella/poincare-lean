Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-55: continuity + assembly — THE TOWER CLOSES

Context: `harness/reports/M5-glob-54_done.md` (READ FIRST). 🎉 THE RESIDUAL LANDED: `chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_data` (`DoublyResidual.lean` — the canonical endpoint field's derivative from the third-variation data, with the full residual layer). THE CLOSING: (1) DISCHARGE its `thirdVariation_data` hypotheses at the hosted datum (the PL solutions `ThirdVariation.lean`, the remainders `FieldC1.lean`, Lipschitz `FlowSmoothness.lean`, the doubly-augmented ODE facts — the `SecondDischarge` instantiation pattern); (2) CONTINUITY of the derivative (the third-variation endpoints Grönwall-continuous in the base — the dependence estimates; or `ContinuousAt` from the same residual bounds); (3) 🎯 `ContDiffAt ℝ 1 (canonical fderiv field)` → `CanonicalC1/LevelThreeFeed`'s bridges → `TowerCloses` → 🎯🎯 THE F-TRANSITION LAW UNCONDITIONAL (both sides — the sphere identically). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-55_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TowerClosed.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TowerClosed` and report the actual result. Commit your work.
