Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-107: the radius tuple — the bounded norm-system data at selector time

Context: `harness/reports/M5-rigid-106_blocked.md` (READ FIRST — the VERBATIM radius tuple). PROVEN: the selector transverse export with alignment + initial identities (`TransverseExport.lean`). THE ONE TUPLE: the bounded norm-system `(radius, rNorm, LNorm, KNorm)`-with-membership at the SELECTOR TIME — the machinery: `ScalarPin.lean`'s `hplNorm` constructors (bounded-center, via `BoundedPackage.lean`), `GronwallMembership.lean`'s membership lemmas (`q`-centered + fixed-radius + bounded-`q` handoff), `UniformShrink.lean`'s ball-uniform bounds — ASSEMBLE at the selector's `T` (the selector time satisfies `T < εlin` — the uniform-shrink data covers it; the coefficient path bounds come from the selector's exported base package). Construct the tuple (source + target), feed `TransverseExport`'s composite → `BlockDiagonal`'s adapter → `A/B` → the consumer → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/RadiusTuple.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-107_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.RadiusTuple` and report the actual result. Commit your work.
