Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-111: bound the scalar Aop — algebra over the flow bound

Context: `harness/reports/M5-rigid-110_blocked.md` (READ FIRST). PROVEN: the radius floors GIVEN `‖Aop‖·T ≤ 1/2` (`FinalSelector.lean`). THE ONE BOUND: the scalar norm-system operator `Aop : Triple →L[ℝ] Triple` — its ENTRIES are built from the SAME coefficient data as the flow operator (the norm-system ODE `a'=2b, b'=c−a, c'=−2b` has CONSTANT small coefficients (!) in the covariant form — CHECK `GronwallMembership/JacobiNormSystem.lean`'s Aop definition: if the system is the constant-coefficient `(2b, c−a, −2b)` triple, then `‖Aop‖` is an ABSOLUTE constant (≤ 4-ish — compute it once, `ContinuousLinearMap.opNorm_le_bound` over the explicit matrix) — NO ball-uniformity needed!); if speed-scaled (`s²`-weighted entries), bound by the speed bound (exported, `SpeedPackage/ThreeBounds.lean`). THEN the shrink `‖Aop‖·T ≤ 1/2` is ONE more ball-radius term (T ∝ ‖v‖ — the proven pattern), and `FinalSelector`'s floors fire → the tuple → the composite → the adapter → `A/B` → 🎯 `cartanMap_isLocalIsometry` — CURVATURE-ONLY. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/AopBound.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-111_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.AopBound` and report the actual result. Commit your work.
