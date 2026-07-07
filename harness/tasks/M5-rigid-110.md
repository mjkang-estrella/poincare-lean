Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-110: the last min term — the shrunk selector closes everything

Context: `harness/reports/M5-rigid-109_blocked.md` (READ FIRST). EXPORTED: the compact coefficient bounds, center bounds, shrink arithmetic adapters, continuations (`ThreeBounds.lean`). THE LAST SELECTOR VARIANT: the common-time selection with `‖Aop‖·T ≤ 1/2` — ONE MORE TERM in the time min (the rigid-96/97/108 arithmetic, final iteration): the scalar norm-system `Aop` bound derives from the exported coefficient bound (`ThreeBounds.lean`'s `Ccoeff` re-export); choose `T` (equivalently the `v`-ball radius) below `1/(2·Ccoeff)` too — REPLAY the selector/common-time theorem (`UniformFlowExport/UniformShrink/SmallTCommon.lean` chain — the latest variant) with the extra bound threaded, and CONCLUDE the Grönwall/speed-pinned radius implications (the continuations in `ThreeBounds/CoefficientShrink.lean` fire). Then EVERYTHING chains: tuple → `TransverseExport` composite → `BlockDiagonal` adapter → `A/B` → the consumer → 🎯 `cartanMap_isLocalIsometry` — for every closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors, some alignment: the pullback equality on a punctured shrunk normal ball — CURVATURE-ONLY. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/FinalSelector.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-110_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.FinalSelector` and report the actual result. Commit your work.
