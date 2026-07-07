Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-112: EVERYTHING QUANTITATIVE IS PROVEN — assemble

Context: `harness/reports/M5-rigid-111_done.md` (READ FIRST) + the chain of reports 105-110. THE COMPLETE QUANTITATIVE INVENTORY: `‖Aop‖ ≤ 4·max(1, speed²)` + shrink corollaries producing `‖Aop‖·T ≤ 1/2` (`AopBound.lean`); the speed bounds (`SpeedPackage/ThreeBounds.lean`); the radius floors given the shrink (`FinalSelector.lean`); the tuple constructor (`CoefficientShrink.lean`); the three-bounds exports + continuations (`ThreeBounds.lean`); the transverse composite (`TransverseExport.lean`); the block-diagonal adapter (`BlockDiagonal.lean`); the selector with all prior min terms (`UniformFlowExport/UniformShrink/CommonTime.lean` chain). THE ASSEMBLY: add the final min term (`T ≤ 1/(2·4·max(1,speedBound²))`-shaped — the ball radius arithmetic, threading the speed bound), instantiate the chain end to end at the selector's datum. 🎯 `cartanMap_isLocalIsometry` — for every closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors `x₀ p₀`, some alignment `L`: the chart-metric pullback equality on a punctured shrunk normal ball — CURVATURE-ONLY hypotheses, NOTHING else. If ONE hypothesis genuinely cannot be fed, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/RigidityComplete.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-112_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.RigidityComplete` and report the actual result. Commit your work.
