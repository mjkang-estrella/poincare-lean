Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-37: the residual export — augmented endpoints produce the fderiv data

Context: `harness/reports/M5-glob-36_blocked.md` (READ FIRST — the VERBATIM fderiv residual + symmetry demands). PROVEN: the uniqueness bridge (`DerivativeUnique.lean` — directional residuals for `fderiv F` ⟹ the DF conclusion); the augmented endpoint derivative at the geodesic data (`SecondDischarge.lean`) + the residual theorem (`SecondFlowDerivative.lean`) + the CLM (`SecondFrechet.lean`). THE EXPORT: (1) THE RESIDUAL — the augmented theorems conclude `HasDerivAt`-shaped facts for the endpoint in the base direction; convert to the RESIDUAL BOUND form the bridge wants (`‖fderiv F(q+δ)(w) − fderiv F(q)(w) − CLM(δ)(w)‖ ≤ ε‖δ‖`-shaped — the `HasDerivAt` remainder unfolding + the direction-uniform machinery — the `IsometryInstantiate/GronwallMembership` conversion patterns); (2) THE SYMMETRY (if `FTransition/LCNaturality` demand `D²F` symmetric): `ContDiff.isSymmSndFDerivAt`-shaped — F is C² once `fderiv F` is differentiable (the conclusion itself!) — Mathlib's `second_derivative_symmetric`-family applies to the twice-differentiable F. FEED → `HasFDerivAt DF` on the ball → `GermAndField/FTransition` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-37_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ResidualExport.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ResidualExport` and report the actual result. Commit your work.
