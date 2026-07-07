Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-25: the target-ray identity — the old map's exp-naturality at x₁

Context: `harness/reports/M5-glob-24_blocked.md` (READ FIRST — the VERBATIM old-map target-ray identity / velocity identification). PROVEN: everything else — the chart bridge fired (`TwoBridges.lean`); the assembler; the reanchor law BOTH SIDES (`ChainRuleInput/NaturalityCascade.lean`); the old map's conjugation at its own anchor (`CartanNormalCoords.lean`); `L₁`'s construction as the differential (`InducedAlignment.lean`). THE COMPOSITION: `Φ_old(exp_{x₁}(t·w))` — (a) express `exp_{x₁}(t·w)` through the `x₀`-data via the SOURCE reanchor law (the shifted germ = the reanchored germ — backwards: the x₁-ray IS the shifted x₀-geodesic); (b) apply the old map's anchor conjugation along the x₀-geodesic (`GeodesicPreservation.lean`'s anchor identity — the old map sends x₀-rays to target rays); (c) re-express the target point through the TARGET reanchor law at `Φx₁`; (d) the resulting velocity = `L₁ w` by `L₁`'s defining construction (the differential action — `InducedAlignment`'s field + the velocity components of the two reanchor laws matching through the chain rule). ASSEMBLE → the target-ray identity → `TwoBridges`' theorem fires → 🎯 `RigidStepCompatibleWith` UNCONDITIONAL → the chain (`CartanChain/CartanContinuation` iteration). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-25_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TargetRayIdentity.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TargetRayIdentity` and report the actual result. Commit your work.
