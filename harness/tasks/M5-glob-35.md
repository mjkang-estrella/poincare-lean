Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-35: the concrete residual — augmented remainders feed the upgrade

Context: `harness/reports/M5-glob-34_blocked.md` (READ FIRST — the VERBATIM concrete residual comparison demanded for the Cartan `DF` field). PROVEN: the abstract upgrade (`clmField_hasFDerivAt_of_residual_norm_le`, `DFrechetUpgrade.lean`); the augmented directional derivatives + remainders (`SecondDischarge/SecondFlowDerivative.lean`); the CLM candidate (`SecondFrechet.lean`); the DF field's defining specs (`DifferentialField.lean`). THE COMPARISON: `‖DF(q+δ) − DF(q) − CLM(δ)‖ ≤ (the augmented remainder bound)·‖δ‖`-shaped — DF's values are the flow-derivative endpoints (the field's spec identifies DF with the linearized endpoints — `LinearizedFamilyExport/CartanCascade` exports); their differences at nearby base data are EXACTLY what the augmented/second-variation remainders control (glob-31's residual theorem — instantiate its conclusion as the bound; the operator-norm form via finite-dim `ContinuousLinearMap.opNorm_le_bound` over the directional bounds — direction-uniformity from the compact-tube machinery). ASSEMBLE → feed the upgrade → `HasFDerivAt DF (CLM) q` on the ball → `GermAndField/FTransition` fire → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-35_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ConcreteResidual.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ConcreteResidual` and report the actual result. Commit your work.
