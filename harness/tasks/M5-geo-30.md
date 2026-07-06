Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-30: interval cutoff-one membership — the length formula and sharp bound land

Context: `harness/reports/M5-geo-29_blocked.md` + the tail of `Poincare/Global/GeodesicLength.lean` (READ BOTH FIRST): the integrand identification is proven UNDER the hypothesis that the flow position stays in the anchor's cutoff-one zone on the interval. The missing export: shrink the flow's velocity ball/time horizon so positions remain in the cutoff-one neighborhood (`cutoff_eventuallyEq_one` gives an open neighborhood of the anchor image where cutoff = 1, `GeodesicTransport.lean`; the target-shrunk endpoint flow (`ExponentialMapDef.lean`) already shrinks positions into the chart target by the SAME continuity/ball argument — replay it against the cutoff-one neighborhood instead/additionally).

Deliverables, in a NEW file `Poincare/Global/GeodesicLengthFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE CUTOFF-ONE FLOW: a further-shrunk uniform flow package whose positions lie in the cutoff-one zone on the whole `Icc` (radius/horizon shrinking; reuse the target-shrunk proof pattern).
2. THE LENGTH FORMULA: `pathELength` of the radial curve on `[0, t]` computed via the constant-speed integrand (compose geo-29's integrand identification, geo-28's regularity, `chart_geodesic_speed_constantOn`).
3. THE SHARP DISTANCE BOUND: `dist x₀ (expAt g x₀ v) ≤ …·√(chart speed)` through `induced_edist_le_pathELength`.
4. Report `harness/reports/M5-geo-30_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicLengthFinal` and report the actual result. Commit your work.
