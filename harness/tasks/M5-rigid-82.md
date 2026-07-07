Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-82: the w-uniform PL package — linearity makes it free

Context: `harness/reports/M5-rigid-81_blocked.md` (READ FIRST — the verbatim uniform `∀ w` package shape). PROVEN: the feed lemmas (`PLNormFeed.lean` — `hplNorm` consumption works once the package exists). THE ONE PACKAGE: shared PL constants `(radius, rNorm, LNorm, KNorm)` valid for ALL `w` simultaneously at the hosted datum. THE KEY: the linearized ODE's COEFFICIENT PATH depends only on the BASE GEODESIC — not on `w` (`GeodesicLinearized.lean`'s system: the RHS is `A(t)·state` with `A(t)` built from Γ at the base point) — so the Lipschitz/norm constants are `w`-UNIFORM AUTOMATICALLY: `LNorm` = the sup of `‖A(t)‖` on the compact interval (continuity of the coefficient path — the base flow is continuous, Γ is continuous (`LocalConnectionRegularity/GeodesicChart.lean`); `IsCompact.exists_forall_ge`-shaped sup extraction); `rNorm/KNorm` similarly from the fixed base data. BUILD the uniform package theorem (one existence statement at the hosted datum, source and target — the target via the same generic route), feed `PLNormFeed.lean`'s lemmas → the transverse blocks land → the bundle completes → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/UniformPL.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-82_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.UniformPL` and report the actual result. Commit your work.
