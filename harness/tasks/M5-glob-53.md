Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-53: the canonical field is C¹ — the residual applied

Context: `harness/reports/M5-glob-52_blocked.md` (READ FIRST). PROVEN: the identification bridge (`LevelThreeFeed.lean` — canonical C¹ transfers to the selected fields); ALL residual ingredients at level three: the third-variation PL (`ThirdVariation.lean`), the doubly-augmented remainders (`FieldC1.lean`), the field regularity/Lipschitz (`FlowSmoothness.lean`), the residual theorem shape (`SecondFlowDerivative.lean`), the ODE instantiation pattern (`SecondDischarge.lean`). THE APPLICATION: (1) the doubly-augmented ODE facts at the hosted data (the augmented flow + its first variation solve the doubly-augmented system — the `SecondDischarge` instantiation one level up); (2) FEED the residual theorem ⟹ `HasFDerivAt (q ↦ fderiv e q) (third-variation endpoint) q` at ball points; (3) CONTINUITY of the third-variation endpoints in `q` (the doubly-augmented Grönwall dependence — the `AugmentedDependence` pattern; the endpoints' differences bounded by the base perturbation) ⟹ 🎯 `ContDiffAt ℝ 1 (q ↦ fderiv e q) …` (differentiable + continuous derivative) — feed `LevelThreeFeed`'s bridge → the selected fields C¹ → `TowerCloses` → 🎯🎯 THE F-TRANSITION LAW. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-53_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/CanonicalC1.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.CanonicalC1` and report the actual result. Commit your work.
