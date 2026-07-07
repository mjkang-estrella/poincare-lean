Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-36: derivative uniqueness — the selected DF is the canonical endpoint

Context: `harness/reports/M5-glob-35_blocked.md` (READ FIRST — the VERBATIM identification demand: the selected `DF (…)` vs the augmented second-variation endpoint family). THE KEY: DERIVATIVE UNIQUENESS — the selected `DF q` is A strict derivative of `F` at `q` (`DifferentialField.lean`'s spec) ⟹ `DF q = fderiv ℝ F q` (`HasStrictFDerivAt.hasFDerivAt` + `HasFDerivAt.fderiv` — derivatives are unique); the canonical flow-derivative endpoint is ALSO the derivative (`ExponentialStrictClose/GeodesicFlowDerivative` route through the linearized endpoint CLM — its strict derivative statements) ⟹ EQUAL. So the identification is: both are `fderiv F q` — a two-line uniqueness chain per point. ASSEMBLE: (1) `DF q = fderiv F q` on the ball; (2) the augmented residuals control `fderiv F` differences (glob-31/32's theorems are ABOUT the canonical objects — now the same as DF); (3) feed `ConcreteResidual/DFrechetUpgrade` → `HasFDerivAt DF (CLM) q` → `GermAndField/FTransition` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-36_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/DerivativeUnique.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.DerivativeUnique` and report the actual result. Commit your work.
