Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-33: the second Fréchet upgrade — HasFDerivAt for the D field

Context: `harness/reports/M5-glob-32_blocked.md` (READ FIRST — the VERBATIM directional-to-Fréchet gap for `HasFDerivAt D`). PROVEN: the augmented endpoint directional derivatives at the geodesic data (`SecondDischarge.lean`); the second-variation linearity (the second-variation system is LINEAR in its own initial data — the `linearODE` structure) and the uniform remainders (`SecondFlowDerivative.lean`'s residual layer). THE UPGRADE (the first-order pattern — `ExponentialFrechet.lean`/`LinearizedCLM.lean`/`ExponentialStrictClose.lean` mirrored at order two): (1) the CANDIDATE second derivative as a CLM: the second-variation endpoint map is linear in the perturbation (additivity/homogeneity by the linear-system uniqueness — the `LinearizedAdditivity.lean` pattern applied to the second-variation system) + finite-dim continuity; (2) the DIRECTIONAL-to-FRÉCHET upgrade: uniform remainders over directions (the compact-tube machinery — the augmented remainders from glob-31/32 are direction-uniform — CHECK and thread) ⟹ `HasFDerivAt (D-field) (the CLM) q` at the ball points; (3) feed `GermAndField/FTransition.lean`'s demand → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-33_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/SecondFrechet.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.SecondFrechet` and report the actual result. Commit your work.
