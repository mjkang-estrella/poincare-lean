Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-31: the second flow derivative — the first-order pattern at order two

Context: `harness/reports/M5-glob-30_done.md` (READ FIRST). PROVEN: the augmented system + second-variation operator + PL package (`SecondVariation.lean`). THE REPLAY (the first-order chain as template — READ `GeodesicDerivative/GeodesicDerivativeFinal/GeodesicFlowDerivative.lean` end to end and mirror): (1) the second-variation solutions exist/unique (the PL package + the `linearODE` machinery — likely already reachable from glob-30's theorem); (2) THE UNIFORM TAYLOR REMAINDERS at second order: the difference of first-variation solutions at nearby base data minus the second-variation approximation is `o(‖δ‖)` — the Grönwall residual argument (`GeodesicDerivativeFinal.lean`'s abstract residual layer is base-agnostic — instantiate with the augmented system); (3) 🎯 THE SECOND FLOW DERIVATIVE: `(base data) ↦ Ψ_w(T)` is differentiable with derivative the second variation — the `GeodesicFlowDerivative.lean` pattern applied to the augmented flow. Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-glob-31_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/SecondFlowDerivative.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.SecondFlowDerivative` and report the actual result. Commit your work.
