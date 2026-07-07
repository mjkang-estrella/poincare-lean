Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-57: endpoint continuity — the C¹ assembly fires

Context: `harness/reports/M5-glob-56_blocked.md` (READ FIRST). PROVEN: the hosted third-variation family `Ω` (`ThirdFamily.lean` — initial value, ODE, invariance); the residual theorem (`DoublyResidual.lean`); the projection (`TowerClosed.lean`); the C¹ bridges (`LevelThreeFeed/CanonicalC1/TowerCloses`). THE CLOSING: (1) feed `Ω`'s facts into `DoublyResidual`'s `thirdVariation_data` at the hosted datum (shape alignment — the family's exports were built to match); (2) ENDPOINT CONTINUITY: `q ↦ (third-variation endpoint at q)` continuous — the Grönwall difference bound between the families at nearby bases (the `AugmentedDependence.lean` pattern at the third-variation system — or the simpler route: the CLM-valued endpoint's continuity from the residual bound itself: `‖endpoint(q+δ) − endpoint(q)‖ ≤ C‖δ‖`-shaped Lipschitz continuity from the dependence estimates — Lipschitz ⟹ continuous, cheap); (3) 🎯 `ContDiffAt ℝ 1 (fderiv e field)` (differentiable via the residual + continuous derivative via (2)) → the bridges fire → 🎯🎯 THE F-TRANSITION LAW UNCONDITIONAL (both sides). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-57_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/EndpointContinuity.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.EndpointContinuity` and report the actual result. Commit your work.
