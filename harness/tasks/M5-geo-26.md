Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-26: strict derivative → exp is a local homeomorphism

Context: `expAt_chart_hasFDerivAt_zero` (`Poincare/Global/ExponentialFrechet.lean`, report `harness/reports/M5-geo-25_done.md` — READ FIRST, incl. the noted inverse-function gap): charted `expAt` has Fréchet derivative `id` at `0`. Mathlib's inverse function theorem consumes `HasStrictFDerivAt` (`HasStrictFDerivAt.toPartialHomeomorph` / `localInverse`). Strict differentiability at `0` is the TWO-VARIABLE little-o: `f y − f x − (y − x) = o(‖y − x‖)` as `(x, y) → (0, 0)` jointly — a strengthened uniform remainder over both base points. The machinery: Lipschitz dependence (`GeodesicDependence.lean` — gives `f y − f x = O(y − x)` uniformly), the flow derivative + its uniform remainder (`GeodesicFlowDerivative.lean`, `GeodesicDerivative.lean` compact-tube uniformity), and the geo-25 velocity-remainder pattern applied at moving base points.

Deliverables, in a NEW file `Poincare/Global/ExponentialLocalHomeo.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE STRICT DERIVATIVE: `HasStrictFDerivAt (fun v ↦ extChartAt I x₀ (expAt g x₀ v)) (ContinuousLinearMap.id ℝ _) 0` — via the two-variable uniform remainder (Heine–Cantor/equicontinuity discipline; if the two-variable upgrade genuinely blocks, isolate the ONE estimate).
2. THE PAYOFF: via `HasStrictFDerivAt.toPartialHomeomorph`, `expAt g x₀` (charted) is a local homeomorphism at `0` — export the PartialHomeomorph and its source-membership/inverse lemmas; then the M-level statement: `expAt g x₀` restricted to a small ball is injective and open onto a neighborhood of `x₀` (compose with the chart homeomorphism; spelling free, semantics frozen).
3. Report `harness/reports/M5-geo-26_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialLocalHomeo` and report the actual result. Commit your work.
