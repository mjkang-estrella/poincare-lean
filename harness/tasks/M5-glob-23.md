Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-23: the ray-cover inputs — decomposition and velocity identification

Context: `harness/reports/M5-glob-22_blocked.md` (READ FIRST — the VERBATIM ray-cover inputs). PROVEN: `rigidStepCompatibleWith_of_common_source_expAt_ray_cover` (`RaysToBall.lean` — the assembler). THE TWO INPUTS: (1) THE POINTWISE RAY DECOMPOSITION: every common-source point `y` = `expAt x₁ (t·w)`-shaped — the exp partial homeomorphism's INVERSE on the ball (`expAtChartOpenPartialHomeomorph` — its `symm` + `left_inv/right_inv` fields give `v_y := homeo.symm y` with `y = homeo v_y`; the ray data `(t, w) = (‖v_y‖, v_y/‖v_y‖)`-shaped via the ray law); (2) THE VELOCITY IDENTIFICATION: the reanchored target velocity at `y`'s parameters = `L₁`'s action on the source ray velocity — from the INDUCED alignment's construction (`InducedAlignment.lean` — `L₁` was BUILT as the differential action; the reanchored velocity IS the differential image by the reanchor law's velocity component — match the two through `ChainRuleInput/NaturalityCascade.lean`'s exports). SUPPLY both at the common-source points → the assembler fires → 🎯 `RigidStepCompatibleWith` UNCONDITIONAL → `CartanChain/CartanContinuation` fire → THE CHAIN THEOREM (continuation along uniform subdivisions). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-23_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/RayCoverInputs.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.RayCoverInputs` and report the actual result. Commit your work.
