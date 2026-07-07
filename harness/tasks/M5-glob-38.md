Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-38: the congruence — fderiv F inherits the endpoint derivative

Context: `harness/reports/M5-glob-37_blocked.md` (READ FIRST). PROVEN: (a) `q ↦ fderiv F q` AGREES with the flow-derivative endpoint family ON THE BALL (`DerivativeUnique.lean`'s pointwise identification); (b) the endpoint family has the augmented derivative at the geodesic data (`SecondDischarge.lean`); (c) the residual/symmetry exports GIVEN `HasFDerivAt (fderiv F)` (`ResidualExport.lean`). THE CONGRUENCE: two functions equal on an OPEN set have the same derivative facts at its points — `Filter.EventuallyEq.hasFDerivAt_iff` (or `HasFDerivAt.congr_of_eventuallyEq`): the ballwise identification gives `(fderiv F) =ᶠ[𝓝 q] (endpoint family)` (eventually_of_mem on the open ball) ⟹ the augmented `HasFDerivAt` TRANSFERS to `fderiv F` ⟹ feed `ResidualExport` → the residual + symmetry → `DerivativeUnique`'s bridge → `HasFDerivAt DF` → `GermAndField/FTransition` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL, and with it F's geodesic preservation opens. ALIGN the shapes (the augmented theorem's conclusion form vs `HasFDerivAt (endpoint family)` — convert derivative forms as needed). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-38_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/CongruenceStep.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.CongruenceStep` and report the actual result. Commit your work.
