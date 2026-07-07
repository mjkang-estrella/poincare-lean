# M5-rigid-36 blocked: strict derivative at nonzero endpoints

## Status

Blocked.  I did not add `Poincare/Global/ExponentialStrictAt.lean`, because the
current exported geodesic-flow derivative surface is directional in a chosen
linearized solution and does not yet provide the continuous-linear endpoint map
or two-variable strict estimate needed for a non-vacuous
`HasStrictFDerivAt` theorem at a nonzero velocity.

## Existing verified inputs

The zero theorem

```lean
GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
```

in `Poincare/Global/ExponentialLocalHomeo.lean` proves strict
differentiability at `0` by a special scaling argument around the zero velocity.
It uses the common PL chart flow from `expAt_uniform_pl_flow_eq_on_Icc` and the
two-base endpoint estimate
`chart_flow_position_pair_sub_linear_norm_le`.

For nonzero base velocity, the strongest exported derivative theorem I found is

```lean
GeodesicTransport.chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
```

in `Poincare/Global/GeodesicFlowDerivative.lean`.  It proves, for fixed
`v`, direction `w`, and a chosen linearized solution `Ψ` with
`Ψ 0 = (0, w)`, the one-dimensional derivative

```lean
HasDerivAt
  (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
  (Ψ t) 0
```

The Cartan wrapper
`CartanIsometry.expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`
projects this to charted `expAt`, again only in the scalar parameter `s` and for
one chosen `Ψ`.

## Missing estimate isolated

The next non-vacuous theorem needed is the following single estimate/package for
the common PL chart flow.  In Lean shape, for the exported
`expAt_uniform_pl_flow_eq_on_Icc` data, every interior base velocity `v` and
fixed positive time `t` should provide a continuous-linear endpoint derivative
`D : E →L[ℝ] E` whose value is the position component of the linearized solution,
and this `D` should satisfy the strict two-variable endpoint remainder:

```lean
-- schematic target estimate
∃ D : E →L[ℝ] E,
  (∀ w : E, ∃ Ψ : ℝ → E × E,
    Ψ 0 = ((0 : E), w) ∧
    (∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) τ (Ψ τ))
        (Icc (-ε) ε) τ) ∧
    D w = (Ψ t).1) ∧
  ∀ c > (0 : ℝ), ∀ᶠ p : E × E in 𝓝 (v, v),
    ‖(α (extChartAt I x₀ x₀, p.1) t).1 -
      (α (extChartAt I x₀ x₀, p.2) t).1 -
      D (p.1 - p.2)‖ ≤ c * ‖p.1 - p.2‖
```

This is exactly the strict derivative estimate for
`fun u => (α (extChartAt I x₀ x₀, u) t).1` at `v`.  Once exported, the existing
`hexp`/target clauses from `expAt_uniform_pl_flow_eq_on_Icc` should transfer it
to `fun u => extChartAt I x₀ (expAt g x₀ u)` after the usual fixed positive
time rescaling.

The current directional theorem proves only the restriction of this statement to
lines `p = (v + s • w, v)`, with `D w` represented by an externally supplied
solution `Ψ`.  It does not prove the map `w ↦ (Ψ_w t).1` is a
`ContinuousLinearMap`, nor the Heine-Cantor/equicontinuity estimate uniform for
two independently varying endpoints `p.1` and `p.2`.

## Required build

Command:

```bash
lake build Poincare.Global.ExponentialStrictAt
```

Actual result: failed, because no non-vacuous
`Poincare/Global/ExponentialStrictAt.lean` module was added.

Final output:

```text
✖ [2/2] Running Poincare.Global.ExponentialStrictAt
error: no such file or directory (error code: 4294967294)
  file: /Users/mjkang/Develop/poincare-wt-M5-rigid-36/Poincare/Global/ExponentialStrictAt.lean
Some required targets logged failures:
- Poincare.Global.ExponentialStrictAt
error: build failed
```
