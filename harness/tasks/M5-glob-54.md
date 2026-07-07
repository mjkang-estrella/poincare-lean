Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-54: LASER — the doubly-augmented residual instantiation ONLY

Context: `harness/reports/M5-glob-53_blocked.md` (READ FIRST — the VERBATIM hosted third-variation residual + dependence demands). ⚠️ SCOPE: this task does EXACTLY ONE THING — replay `SecondDischarge.lean`'s instantiation ONE LEVEL UP. READ `SecondDischarge.lean` END TO END (how it instantiated `SecondFlowDerivative`'s residual theorem at the AUGMENTED data: the ODE facts it built, the shapes it fed). REPLAY: the DOUBLY-augmented ODE facts at the hosted data — the augmented flow (`SecondDischarge`'s own exports give the augmented solution) paired with its first variation (the second-variation PL solutions, `SecondVariation.lean`) solves the doubly-augmented system (`FlowSmoothness/ThirdVariation.lean`'s field) — verify by substitution (the same algebra `SecondDischarge` did); FEED the residual theorem (`SecondFlowDerivative.lean` — its abstract form applies to ANY system meeting its hypotheses: the third-variation PL (`ThirdVariation`), the remainders (`FieldC1`), Lipschitz (`FlowSmoothness`)) ⟹ 🎯 `HasDerivAt/HasFDerivAt`-shaped: the augmented-flow endpoint (= the canonical `fderiv e` field, by the proven identifications) has the third-variation endpoint as derivative at the hosted data. NOTHING MORE — no continuity, no C¹ assembly (next task). Report `harness/reports/M5-glob-54_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/DoublyResidual.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.DoublyResidual` and report the actual result. Commit your work.
