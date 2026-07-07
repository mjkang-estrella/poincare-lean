Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-21: the naturality cascade — RigidStepCompatible from the reanchor law

Context: `harness/reports/M5-glob-20_done.md` (READ FIRST). 🎉 THE REANCHOR LAW IS UNCONDITIONAL (`shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_..._unconditional`, `ChainRuleInput.lean`). THE CASCADE (each consumer proven, awaiting this input): (1) the reanchor law gives the OLD germ near `x₁` re-expressed through `x₁`-anchored exponential data — feed `ReanchorLawFinal.lean`'s assembly (its remaining hypothesis WAS this law — check shapes) → the old-germ re-centering; (2) `GeodesicPreservation.lean`'s anchor identity + the re-centering → the off-anchor naturality (`OffAnchorNaturality.lean`'s bridge — its `RigidStepCompatibleWith` input now derivable — CHECK the exact circularity: the bridge consumed compatibility; the DIRECT route: reanchor law + conjugation → the carried germ near x₁ = exp∘L_ind∘exp⁻¹ = the re-anchored germ → `EqOn` on the overlap); (3) → `ExpNaturality.rigidStepCompatibleWith_of_target_chart_exp_naturality` fires → `RigidStepCompatibleWith`; (4) → `CartanChain`'s iteration (`chain_step_restr_eqOnSource` + `CartanContinuation.twoStep_*`) along uniform subdivisions (`UniformNormalRadius.lean`) → 🎯 THE CHAIN THEOREM: continuation along any path with germ agreement at each step. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-21_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/NaturalityCascade.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.NaturalityCascade` and report the actual result. Commit your work.
