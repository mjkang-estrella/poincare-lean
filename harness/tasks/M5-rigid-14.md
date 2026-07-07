Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-14: PIN FIRST, THEN PROVE — the bilinear endpoint expansion

Context: `harness/reports/M5-rigid-13_blocked.md` (READ FIRST): the remaining bridge is the FULL BILINEAR endpoint metric expansion for arbitrary `u, u'` from the interval-scoped directional facts. ⚠️ MANDATORY SANITY CHECK BEFORE PROVING (the campaign's refutation protocol — two frozen targets died without it): the demanded identity involves the CHART metric AT THE ENDPOINT paired against sin-Jacobi values, versus the ANCHOR pairing — and the chart metric VARIES along the geodesic (our charts are not normal coordinates). PIN the statement against the ROUND SPHERE's explicit data: stereographic conformal factor `16/(‖z‖²+4)²` (`RoundSphereChart.lean`), explicit geodesics through the anchor (great circles through the stereographic origin — the anchor image is the chart origin where the factor is 1), and check the proposed expansion identity numerically/symbolically at a nonzero endpoint. If FALSE as shaped, derive the CORRECTED endpoint-weighted form (the pullback identity only needs both sides to share the SAME correction — document and reshape the bundle constructor target accordingly; sanctioned correction with derivation).

Then deliverables, in a NEW file `Poincare/Global/CartanExpansionBridge.lean` (+ sanctioned ADDITIVE edits to `CartanLocalIsometry.lean` only if the bundle target must be reshaped — no breaking changes):
1. The pinned/corrected bilinear endpoint expansion statement + its proof from the interval facts (polarization over the directional cases + the Gram decomposition from `CartanPullback.lean`).
2. Both-side instantiation → 🎯 THE UNCONDITIONAL LOCAL ISOMETRY on the normal ball (or the corrected-form equivalent that the pullback identity consumes).
3. Report `harness/reports/M5-rigid-14_{done|blocked}.md` INCLUDING the pinning computation's outcome.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge` and report the actual result. Commit your work.
