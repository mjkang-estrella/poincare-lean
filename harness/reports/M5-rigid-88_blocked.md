# M5-rigid-88 blocked: enriched same-`α` feed lands, norm membership still not exported

## Status

Added `Poincare/Global/IsometryComplete.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The rigid-86 base-curve gap is closed for the source-side assembly shape:
`EnrichedCascade.BaseCurvePackage` and
`EnrichedCascade.LinearizedFamilyPackage` now feed the same hosted `α` into
the one-sided orthogonality payload and then into the source
`SolutionsFeed.source_transverseTransverse_of_solutions_feed` consumer.

## What landed

- `IsometryComplete.chartGeodesicMetric_differentiableAt`
  exposes the chart-metric differentiability fact needed by one-sided payload
  consumers; the reusable theorem in `GeodesicSpeed.lean` is private.
- `IsometryComplete.source_orthogonal_of_enriched_packages`
  uses the enriched source base and linearized packages to produce the
  one-sided endpoint orthogonality feed for every initially source-anchor
  orthogonal direction.
- `IsometryComplete.target_orthogonal_of_enriched_packages`
  proves the analogous target-side one-sided orthogonality feed.
- `IsometryComplete.source_transverseTransverse_of_enriched_solutions_feed`
  applies `SolutionsFeed.source_transverseTransverse_of_solutions_feed` with
  the enriched base derivative, target, cutoff, speed, endpoint, linearized
  derivative, and one-sided orthogonality fields.

## First unfed field

I did not state the curvature-only `cartanMap_isLocalIsometry` theorem.  After
the enriched packages are used, the first remaining source-side field not
exported by the cascade or the named radial/speed/one-sided packages is the
global norm-system closed-ball membership required by `SolutionsFeed`:

```lean
(hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
  (JacobiNormSystem.normA g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ w τ).1) s,
    JacobiNormSystem.normB g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ w τ).1)
      (fun τ : ℝ =>
        (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
          (γ τ).2 (Ψ w τ).1) s,
    JacobiNormSystem.normC g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ =>
        (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
          (γ τ).2 (Ψ w τ).1) s) ∈
    closedBall ((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) radius)
```

Assuming this inside a final `cartanMap_isLocalIsometry` wrapper would simply
rename the missing norm-membership package, so the final theorem is not stated
here.

## Verification

- `lake build Poincare.Global.IsometryComplete`
  - Result: success.
  - Final lines:

```text
✔ [3196/3196] Built Poincare.Global.IsometryComplete (3.4s)
Build completed successfully (3196 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/IsometryComplete.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/IsometryComplete.lean`
  - Result: success.
