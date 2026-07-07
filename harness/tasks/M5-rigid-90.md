Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-90: the a-priori Grönwall membership — no circularity

Context: `harness/reports/M5-rigid-89_blocked.md` (READ FIRST): the pinned-value route is CIRCULAR (the pinned theorem consumes `hmem`); the fixed-radius `∀ w` needs `q(w)`-uniformity. THE HONEST ROUTE: (1) A-PRIORI GRÖNWALL — the norm-system state solves a linear ODE with coefficients bounded on the compact interval (the coefficient path from the base geodesic — `GeodesicLinearized.lean`'s structures; the Grönwall machinery `GeodesicDependence/GeodesicDerivative.lean`): `‖state(t)‖ ≤ ‖state(0)‖·e^{C·t} ≤ ‖state(0)‖·e^{C·T}` — membership in the closed ball of radius `‖state(0)‖·e^{CT}` with NO reference to pinned values; (2) BOUNDED `w`: on the `w`-ball (rigid-83's bounded feed — `SolutionsFeed`'s bounded layer + homogeneous extension), `‖state(0)‖ = q(w) ≤ q_max` (continuity of the anchor metric on the compact ball — sup extraction), giving ONE radius for the ball; homogeneity extends the resulting formulas to all `w` (rigid-83/85 pattern — the extension lemmas EXIST). Feed the membership → `SolutionsFeed` completes → the assembly (`IsometryComplete.lean`'s feeds) → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/GronwallMembership.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-90_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.GronwallMembership` and report the actual result. Commit your work.
