Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-20: the chain-rule input — THE REANCHOR LAW unconditional

Context: `harness/reports/M5-glob-19_done.md` (READ FIRST — the VERBATIM remaining chain-rule input). PROVEN: the reanchor germ equality modulo the chain rule (`shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_...`, `SideConditions.lean`). THE INPUT: the first/second-order chain rule along the germ — `(σ∘γ)'(s) = Dσ(γ s)(γ' s)` (+ the second-order form if demanded) — from: the germ's derivative facts (`geodesicGermAt_chart_hasDerivAt` — the germ has the velocity derivative), σ smooth (`HdiffInstantiate.lean` derived the transition smoothness — REUSE), `HasFDerivAt.comp`/`HasDerivAt.scomp` composition lemmas; the second-order form from differentiating again (the germ's second derivative = the geodesic equation; `D²σ` from smoothness). SUPPLY it → 🎯 THE REANCHOR LAW unconditional on the zone → feed `OffAnchorNaturality/ExpNaturality` → `RigidStepCompatibleWith` (via `InducedAlignment`'s compatible step) → THE CHAIN FIRES (`CartanChain` iteration along uniform subdivisions — `CartanChain/UniformNormalRadius.lean`). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-20_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ChainRuleInput.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ChainRuleInput` and report the actual result. Commit your work.
