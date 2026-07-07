Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-5: the curvature bridge on the cutoff-one zone — the oscillator extends along the curve

Context: `harness/reports/M5-rigid-4_blocked.md` (READ FIRST). The anchor-level constant-curvature identity is proven (`JacobiInstantiate.lean`); the oscillator needs it AT EVERY POINT `γ(t).1` along the chart geodesic. The curvature bridge (`ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp` and its chain 3/4/5) was STATED at the anchor image, but its INGREDIENTS are neighborhood-level: the eventual-agreement bridge, cutoff-1 coefficient lemmas (`GeodesicReanchor.lean`: blended = transported chart metric ON the zone), extend-field germ lemmas. TASK: extend the bridge statement from `extChartAt I x₀ x₀` to arbitrary `z` in (a neighborhood inside) the cutoff-one zone — the same term-by-term proof with the anchor-point facts replaced by their zone versions (where a zone version is missing, prove it — the `_apply_chart`/`congr_of_eventuallyEq` lemmas in ChartCurvatureBridge3/4/5 are anchored: check which genuinely used "at the anchor" and which only used zone membership).

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridgeZone.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE ZONE BRIDGE: the chart curvature of `chartChristoffelField g x₀` at `z` in the zone = (identification of) `curvatureOp g.leviCivita` on suitable fields at `(extChartAt I x₀).symm z` (spelling per the anchor version; document what changes).
2. THE ZONE KN IDENTITY for constant-curvature-1 metrics (rigid-4's anchor identity, now at zone points).
3. If reachable: feed into the oscillator (the covariant Jacobi second-derivative theorem holds along the curve) — `J'' = −J` on an honest interval; else isolate the final glue.
4. Report `harness/reports/M5-rigid-5_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ChartCurvatureBridgeZone` and report the actual result. Commit your work.
