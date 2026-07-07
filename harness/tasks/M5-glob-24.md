Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-24: the two bridges — chart-to-manifold and the velocity pointwise

Context: `harness/reports/M5-glob-23_blocked.md` (READ FIRST — the two VERBATIM gaps). PROVEN: the chart-coordinate ray identities (`RayCoverInputs.lean`) + the assembler (`RaysToBall.lean`). BRIDGE (1) CHART-TO-MANIFOLD: from the chart inverse identity to `expAt g x₁ v = y` — `expAt` is DEFINED through the chart (`ExponentialMap/ExponentialMapDef.lean` — READ the definition: `expAt = chart.symm ∘ (chart germ flow)`-shaped); the chart's `left_inv/right_inv` (the `extChartAt` PartialEquiv laws on the source) convert the chart-coordinate identity to the manifold identity — near-definitional unfolding + the source-membership side conditions (the shrunk ball is inside the chart source). BRIDGE (2) THE VELOCITY IDENTIFICATION: the old map's differential at `x₁` acts on the ray velocity as `L₁` — `L₁` was CONSTRUCTED as that differential action (`InducedAlignment.lean` — its defining field: READ and extract the pointwise action equality; the reanchored velocity equals the differential image by `ChainRuleInput`'s velocity component). SUPPLY both → the assembler fires → 🎯 `RigidStepCompatibleWith` → the chain (`CartanChain/CartanContinuation`). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-24_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TwoBridges.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TwoBridges` and report the actual result. Commit your work.
