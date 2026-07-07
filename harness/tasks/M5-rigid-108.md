Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-108: the coefficient-time shrink — ‖Aop‖·T ≤ 1 by ball choice

Context: `harness/reports/M5-rigid-107_blocked.md` (READ FIRST — the VERBATIM `‖Aop‖·T ≤ 1` bound). PROVEN: the obstruction analysis (`RadiusTuple.lean`). THE SHRINK (the rigid-97 pattern EXACTLY): (1) the coefficient operator norm `‖Aop‖` along the selector's base curve is bounded by a BALL-UNIFORM constant `C` (the coefficient path lives on the compact tube — `UniformShrink.lean`'s ball-uniform coefficient bound machinery PROVED this shape for the εlin bound; reuse/extend); (2) the selector time `T = T(v)` is proportional to `‖v‖` — SHRINK the `v`-ball so `T(v)·C ≤ 1` for every `v` in the final ball (radius `≤ (δ/2)/C`-shaped — the same arithmetic as rigid-97's `T < εlin_min`); (3) with the bound, the radius tuple CONSTRUCTS (rigid-107's analysis shows the side conditions are then satisfiable — feed `ScalarPin`'s constructors + `GronwallMembership`); (4) thread through `TransverseExport` → `BlockDiagonal` → `A/B` → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/CoefficientShrink.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-108_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CoefficientShrink` and report the actual result. Commit your work.
