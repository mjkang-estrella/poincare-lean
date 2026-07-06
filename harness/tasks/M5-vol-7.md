Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-7: GOAL 10 — the anti-Lipschitz lower bound, then volume positivity

Context: `harness/reports/M5-vol-6_blocked.md` (READ FIRST) isolates ONE lemma behind unconditional volume positivity: `LocalChartAntilipschitzLowerBound` — the inverse chart is anti-Lipschitz (distance bounded BELOW) on a small chart ball w.r.t. the induced Riemannian distance. This is the MIRROR of the proven Lipschitz direction (`Poincare/Global/VolumeFinitenessComparison.lean` — its 5-step PathELength segment route bounds distance ABOVE). The lower bound classically comes from: any path between two points must traverse the chart; its `pathELength` w.r.t. the blended/chart metric dominates a constant times the Euclidean chart distance (positive-definiteness of the metric on a compact chart ball gives a uniform lower eigenvalue bound; Mathlib's `Riemannian/PathELength.lean` may have the lower-comparison internally — mine `eventually_edist_le_riemannianEDist`-shaped lemmas or the definitional infimum). The consumer `volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound` is already proven (`Poincare/Global/NormalizedFlow.lean`).

Deliverables, in a NEW file `Poincare/Global/VolumePositivity.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE LOWER BOUND: discharge `LocalChartAntilipschitzLowerBound` (exact statement from the blocked report; spelling adaptations documented) for every closed `g` and anchor.
2. THE PAYOFF: `theorem volumeMeasure_univ_ne_zero (g) [Nonempty M] : volumeMeasure g Set.univ ≠ 0` (or the report's exact target shape) via the existing consumer.
3. Report `harness/reports/M5-vol-7_{done|blocked}.md`; if blocked, ONE isolated statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.VolumePositivity` and report the actual result. Commit your work.
