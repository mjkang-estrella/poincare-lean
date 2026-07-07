Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-15: the source-side weighted expansion — the corrected local isometry closes

Context: `harness/reports/M5-rigid-14_blocked.md` (READ FIRST — including the pinning computation and the CORRECTED weighted form). The unweighted expansion was REFUTED (counterweight 1/4 at stereographic radius 2); `CartanExpansionBridge.lean` proves: the corrected endpoint chart-weight theorem, the TARGET-side weighted expansion for `roundSphereMetric3` (unconditional), and the corrected local-isometry consumer awaiting ONE input: the SOURCE-side weighted full bilinear endpoint expansion for `g` with `HasConstantSectionalCurvature3 g 1`, derived from the interval facts. KEY INSIGHT: the weight is a CHART-METRIC quantity; the source's chart metric at the endpoint relates to the anchor metric through the SAME structures the target computation used — the target proof is the TEMPLATE (it used the sphere's constant curvature through the generic machinery, or explicit data? READ ITS PROOF: if it used explicit conformal data, the source version needs the generic route: the weighted expansion should follow from the interval directional facts (radial/transverse/cross + Jacobi sin + constant speed) PLUS the endpoint chart-weight identity — which for a general constant-curvature-1 metric comes from the same Jacobi/Gauss machinery: the chart metric coefficients along the geodesic are determined by the Jacobi fields (they ARE the differentials of exp) — i.e. the weight identity is the Jacobi-pairing evaluation: G(z(t))(J_w(t), J_{w'}(t)) computed via the flow derivative = the s-derivative pairing, whose t-derivative the transverse Gauss variation identity controls — integrate).

Deliverables, in a NEW file `Poincare/Global/CartanSourceExpansion.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE SOURCE WEIGHTED EXPANSION (the exact remaining hypothesis of the corrected consumer).
2. 🎯 THE UNCONDITIONAL CORRECTED LOCAL ISOMETRY (instantiate the consumer).
3. Report `harness/reports/M5-rigid-15_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanSourceExpansion` and report the actual result. Commit your work.
