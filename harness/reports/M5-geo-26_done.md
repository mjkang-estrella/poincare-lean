# M5-geo-26 done

## Scope

Added `Poincare/Global/ExponentialLocalHomeo.lean` only.  No existing Lean
module or root import file was edited.

## Results

- Proved the two-base-point chart-flow endpoint estimate
  `chart_flow_position_pair_sub_linear_norm_le`.
- Proved the strict derivative
  `expAt_chart_hasStrictFDerivAt_zero`:
  `HasStrictFDerivAt (fun v => extChartAt I x₀ (expAt g x₀ v))
    (ContinuousLinearMap.id ℝ _) 0`.
- Packaged the inverse-function-theorem payoff as
  `expAtChartOpenPartialHomeomorph`, with source/target membership,
  local left/right inverse, charted neighborhood-image lemmas, and
  `expAt_chart_map_nhds_zero_eq`.
- Proved the manifold-level small-ball payoff
  `expAt_injective_open_image_smallBall`: for some `r > 0`,
  `expAt g x₀` is injective on `ball 0 r`, its image is open in `M`,
  and that image is a neighborhood of `x₀`.

## Verification

Command:

```bash
lake build Poincare.Global.ExponentialLocalHomeo
```

Result:

```text
Build completed successfully (2843 jobs).
```

The build replayed pre-existing warnings in upstream modules; no new error
remained in `Poincare.Global.ExponentialLocalHomeo`.
