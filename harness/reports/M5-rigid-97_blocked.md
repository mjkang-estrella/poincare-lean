# M5-rigid-97 blocked: uniform PL shrink proved, enriched selector still lacks exported flow data

## Status

Added `Poincare/Global/UniformShrink.lean`. No existing Lean files were edited,
including `Poincare.lean`.

The new module proves the non-vacuous uniform shrink:

- `UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package`

This theorem bounds
`q ↦ linearizedGeodesicFlowOperator (chartChristoffelField g x₀) q` on the
single closed ball exported by `EnrichedCascade.BaseCurvePackage`, then chooses

```lean
εlin = min ε₀ (1 / (4 * ((Lip : ℝ) + 1)))
```

from that ball coefficient bound. The resulting zero-centered PL package is
valid for every hosted base curve in the ball, uniformly in `T`, `α`, and `v`.

It also proves the common-time order fix:

- `UniformShrink.exists_common_time_with_uniform_linearized_pl_and_basic_selectors`

This replays the source/target common-time selection with the two uniform
linearized margins known first, then chooses

```lean
T = min εs (min εt (min εlinS εlinT)) / 2
```

so both exported inequalities are available before the final endpoint ball is
shrunk:

```lean
T < εlin_source
T < εlin_target
```

For every `v` in the final ball, it exports the source and target
`BaseCurvePackage`s, the two concrete zero-centered PL packages on the uniform
linearized intervals, and the basic selected linearized families from
`PLPackages.exists_selected_linearized_family_of_zero_centered_pl_package`.

## Remaining blocker

The enriched `IntervalAlign` selector still cannot be applied from the current
public common-time API.

The selector needs the underlying uniform-flow facts:

```lean
hα0 : ∀ v₀, ‖v₀‖ < δ →
  α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀)

hαder : ∀ v₀, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
  HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀)) ...

hαmem : ∀ v₀, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
  α (extChartAt I3 x₀ x₀, v₀) s ∈ closedBall ...

hαtarget : ∀ v₀, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
  (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target

hexp : ∀ v₀, ‖v₀‖ < δ → ∀ s ∈ Icc 0 ε,
  expAt g x₀ (s • v₀) =
    (extChartAt I3 x₀).symm (α (extChartAt I3 x₀ x₀, v₀) s).1
```

`CommonTime.exists_shrunk_cutoff_one_strictDeriv_package_for_smaller_time`
constructs those facts internally, but exports only:

```lean
EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v
```

and the conditional full-interval selector:

```lean
∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
  IsPicardLindelof ... (tmin := -εs) (tmax := εs) ... →
    ∃ Ψ, ...
```

The new uniform PL package is deliberately on the smaller interval
`[-εlin_source, εlin_source]` with `εlin_source ≤ εs`, so it cannot feed that
full-`εs` conditional. The basic PL selector does fire on the smaller interval,
but it does not export `EnrichedCascade.LinearizedFamilyPackage`, the strict
endpoint derivative, or the radial ray identity. Consequently the master bundle
still lacks:

```lean
hSourceRay : (PsiS v T).1 = T • Vs
hTargetRay : (PsiT (align v) T).1 = T • Vt
```

and the final `cartanMap_isLocalIsometry` assembly is not closed in this file.

## Verification

- Contract-token scan on `Poincare/Global/UniformShrink.lean`
  - Result: no output.
- `git diff --check -- Poincare/Global/UniformShrink.lean`
  - Result: success.
- `lake build Poincare.Global.UniformShrink`
  - Result: success. The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3204/3204] Built Poincare.Global.UniformShrink (3.5s)
Build completed successfully (3204 jobs).
```
