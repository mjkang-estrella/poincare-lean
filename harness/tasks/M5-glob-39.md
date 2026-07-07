Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-39: ASSEMBLE — the F-transition law unconditional

Context: `harness/reports/M5-glob-38_done.md` + the chain of reports glob-27..38 (READ the done ones). EVERY LINK IS PROVEN: the augmented endpoint derivative at the geodesic data (`SecondDischarge.lean`), the ballwise identification (`DerivativeUnique.lean`), the congruence transfer + residual/symmetry package (`CongruenceStep/ResidualExport.lean`), the directional-to-DF bridge (`DerivativeUnique/ConcreteResidual/DFrechetUpgrade.lean`), the F-transition composition (`FTransition.lean` + `GermAndField.lean`'s germs). THE ASSEMBLY: at the punctured-ball datum, instantiate the chain end to end: augmented derivative → congruence → residual+symmetry → `HasFDerivAt DF` → the differentiated pullback (`GermAndField`) → `FTransition`'s composition → 🎯 THE F-TRANSITION LAW UNCONDITIONAL (the target Christoffels pull back under F, signed, on the punctured shrunk ball — curvature-only hypotheses). If ONE shape resists, isolate verbatim. Report `harness/reports/M5-glob-39_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/FTransitionDone.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.FTransitionDone` and report the actual result. Commit your work.
