Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-36: uniform normal radius on compact manifolds

Context: per-anchor normal-neighborhood data is complete: `expAt_injective_open_image_smallBall` (`ExponentialLocalHomeo.lean`), sharp distance bounds (`GeodesicLengthFinal.lean` upper, `AntilipschitzMathlib.lean` lower: `exists_expAt_dist_lower_bound_ball`), all with per-anchor radii `r(x₀) > 0`. On compact `M`, the classical uniformization: a single `r > 0` works for every anchor.

Route (honest options — pick what closes, document): (a) DIRECT COMPACTNESS SWEEP: the per-anchor existence statements are `∃ r > 0, P x₀ r`; extract an open cover by "anchors near x₀ inherit a radius" — this needs the radii to work for NEIGHBORING anchors (a continuity-in-anchor statement the current per-anchor proofs may not expose — assess honestly); (b) THE METRIC-BALL FORM: uniformize only what downstream needs — e.g. `∃ r > 0, ∀ x : M, (metric ball x r) ⊆ (expAt image / chart source)` via the Lebesgue-number lemma (`lebesgue_number_lemma` in Mathlib) applied to the open cover by chart sources / normal images — Lebesgue numbers need only the OPEN COVER, not continuity in the anchor, and give the uniform radius in the INDUCED METRIC (which `MetricCompleteness.lean` + compactness make available). Route (b) is the intended reuse-first path.

Deliverables, in a NEW file `Poincare/Global/UniformNormalRadius.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE UNIFORM RADIUS: `∃ r > 0, ∀ x : M, Metric.ball x r ⊆ (the normal image of x)`-shaped (in `g.toMetricSpace`; exact packaging per route (b); CompactSpace M hypothesis).
2. Payoff lemmas as they compose cheaply: every pair of points at distance `< r` lies in a common normal neighborhood.
3. Report `harness/reports/M5-geo-36_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.UniformNormalRadius` and report the actual result. Commit your work.
