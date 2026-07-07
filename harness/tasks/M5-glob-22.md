Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-22: rays to the ball — the full EqOn

Context: `harness/reports/M5-glob-21_blocked.md` (READ FIRST — the VERBATIM upgrade demand: one-dimensional shifted germ reanchoring → the full common-source `EqOn`). PROVEN: the paired source/target reanchoring along rays (`NaturalityCascade.lean`) + the unconditional reanchor law. THE UPGRADE: every point of the (punctured shrunk) normal ball at `x₁` IS on an exponential ray — `y = exp_{x₁}(t·w)` for the ray through `w = exp⁻¹(y)/‖…‖`-shaped (the exp chart is a PARTIAL HOMEOMORPHISM — `expAtChartOpenPartialHomeomorph`/`ExponentialLocalHomeo.lean` — the inverse EXISTS on the ball; the ray identity applies at the parameters of `y`) — so a map equality proven ALONG EVERY RAY holds AT EVERY BALL POINT: pointwise assembly (take `y`, produce its ray data via the homeo inverse, apply the ray identity at those parameters). ASSEMBLE the ball `EqOn` from the ray identities → the re-centering EqOn → `RigidStepCompatibleWith` (`InducedAlignment/ExpNaturality.lean`'s consumers) → 🎯 THE CHAIN (`CartanChain/CartanContinuation` fire along uniform subdivisions). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-22_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/RaysToBall.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.RaysToBall` and report the actual result. Commit your work.
