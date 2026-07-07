Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-34: HasFDerivAt D — the residual upgrade at order two

Context: `harness/reports/M5-glob-33_blocked.md` (READ FIRST — the VERBATIM `HasFDerivAt D` bridge). PROVEN: the second-variation endpoint CLM (`SecondFrechet.lean`); the augmented directional derivatives at the geodesic data (`SecondDischarge.lean`); the residual/Grönwall layer at order two (`SecondFlowDerivative.lean`). THE UPGRADE (the `ExponentialStrictClose.lean` pattern at order two — READ that proof end to end and mirror): the residual comparison with the CLM candidate — the difference `D(q + δ) − D(q) − CLM(δ)` is controlled by the direction-uniform augmented remainders (glob-31/32's — CHECK direction-uniformity; the compact-tube machinery makes remainders uniform over the perturbation ball) ⟹ `o(‖δ‖)` ⟹ `HasFDerivAt D (CLM) q` at ball points. FEED `GermAndField/FTransition.lean` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL → then geodesic preservation (`SideConditions/ChainRuleInput` pattern with F) is next. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-34_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/DFrechetUpgrade.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.DFrechetUpgrade` and report the actual result. Commit your work.
