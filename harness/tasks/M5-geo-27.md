Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-27: geodesics realize the induced distance locally

Context: normal neighborhoods exist (`expAt_injective_open_image_smallBall`, `Poincare/Global/ExponentialLocalHomeo.lean`); constant speed (`GeodesicSpeed.lean`); the Gauss pairing laws (`GaussLemmaIntegrated.lean`, radial in `GaussLemmaRadial.lean`); the induced distance is Mathlib's path-infimum Riemannian distance (`RiemannianContext.lean` → `EMetricSpace.ofRiemannianMetric`, `Mathlib/Geometry/Manifold/Riemannian/{Basic,PathELength}.lean` — mine the pathELength API used in `VolumeFinitenessComparison.lean`).

THE CLASSICAL TARGET (the Gauss lemma's purpose): within a normal ball, the radial geodesic from `x₀` to `expAt g x₀ v` has length `≤` any competing path — i.e. `dist x₀ (expAt g x₀ v)` (in `g.toMetricSpace`) `= (the g-norm of v)`-shaped, for `‖v‖` small. FULL minimality needs the polar decomposition of arbitrary paths (Gauss lemma splits path speed into radial + transverse parts, transverse ≥ 0). HONEST SLICING — deliver in order, stop where it blocks:
1. UPPER BOUND (should close): `dist x₀ (expAt g x₀ v) ≤ C·‖v‖` and the sharp form `≤ sqrt(G z₀ v v)`-shaped via the geodesic path's `pathELength` = constant-speed integral (the geodesic IS a path; its e-length computes via constant speed — mine how PathELength measures curves and feed the germ curve in).
2. RADIAL ENERGY LOWER BOUND inside the normal ball: any path from `x₀` leaving the chart ball has `pathELength ≥` (uniform lower comparison — the anti-Lipschitz-flavored bound; if this re-hits the parked vol-7 wall, SAY SO and isolate the shared estimate — solving it here would ALSO unblock volume positivity).
3. THE LOCAL DISTANCE FORMULA if 1+2 compose.
4. Report `harness/reports/M5-geo-27_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/GeodesicDistance.lean` (do NOT edit existing files, incl. `Poincare.lean`). No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicDistance` and report the actual result. Commit your work.
