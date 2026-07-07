Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-58: LASER — Ω instantiated and the Grönwall bound, ONLY

Context: `harness/reports/M5-glob-57_blocked.md` (READ FIRST — the VERBATIM two demands). ⚠️ SCOPE: EXACTLY TWO FACTS, nothing else: (1) THE Ω INSTANTIATION: `ThirdFamily.exists_hosted_thirdVariation_solution_family_on_pl_closedBall` instantiated at the hosted datum (the continuous doubly-augmented base curve — from `SecondDischarge/FlowSmoothness`'s exports; the PL data from `ThirdVariation.lean`) — producing the concrete `Ω` with its facts in the shapes `DoublyResidual/EndpointContinuity` consume; (2) THE GRÖNWALL ENDPOINT BOUND: `‖Ω-endpoint(q+δ) − Ω-endpoint(q)‖ ≤ C·‖δ‖` — two third-variation solutions at nearby bases differ Grönwall-boundedly (the `AugmentedDependence.lean` proof pattern at the third-variation system — the linear-system difference obeys the inhomogeneous Grönwall with the coefficient-difference driving term, bounded by the base difference via the coefficients' Lipschitz dependence (the doubly-augmented field's `ContDiff` regularity, `FlowSmoothness/FieldC1.lean`)). Report `harness/reports/M5-glob-58_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/OmegaGronwall.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.OmegaGronwall` and report the actual result. Commit your work.
