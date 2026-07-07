Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-9: radial/transverse decomposition + the Cartan chain rule — the pullback identity

Context: `harness/reports/M5-rigid-8_blocked.md` (READ FIRST). Proven: the chart derivative/Jacobi bridge `expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul` (`CartanIsometry.lean`) — `D(expAt)` on transverse directions = `sin t · w`. THREE named pieces remain (per the report): (1) the radial/transverse DECOMPOSITION of a chart vector against `v` with the Gram algebra (orthogonal projection onto `span v` in the chart metric — elementary inner-product algebra; the chart metrics and their positivity are in `CartanMap.lean`); (2) the FULL `D(expAt)` action: radial factor 1 (`expAt_chart_hasDerivWithinAt_of_norm_lt`/ray-law derivative, `ExponentialRayLaw.lean`), transverse factor `sin‖v‖/‖v‖` (from the bridge with `t = ‖v‖` and the homogeneity rescaling), zero cross terms (Gauss orthogonality, `GaussLemmaIntegrated.lean`); (3) the CHAIN RULE through `cartanMap = expAt_{p₀} ∘ L ∘ (expAt_{x₀})⁻¹` (the PartialHomeomorph derivative composition; `L` intertwines anchor metrics by `TangentAlignment`).

Deliverables, in a NEW file `Poincare/Global/CartanPullback.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1-3 as above, then: THE PULLBACK IDENTITY — `(roundSphere chart metric at Φ-image)(DΦ u, DΦ u') = (g chart metric at source)(u, u')` on the normal ball (both sides decompose with THE SAME factors; `L` aligns the anchors) — the LOCAL ISOMETRY statement (spelling free, semantics frozen).
4. Report `harness/reports/M5-rigid-9_{done|blocked}.md`; strict-partial with ONE isolated piece valid.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanPullback` and report the actual result. Commit your work.
