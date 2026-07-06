# M5-geo-28 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/GeodesicPathLength.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module proves the interval-level regularity part of the radial
PL-flow curve used by `expAt`, plus the interior chart-speed constancy that
will feed the length computation. It does not prove the exact
`pathELength` formula or the sharp distance upper bound, because the current
API still lacks the bridge from the inverse-chart path's manifold
`mfderiv` norm to the chart-metric speed integrand.

## Added declarations

```lean
theorem Poincare.GeodesicTransport.plFlowState_contDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t) :
    ContDiffOn ℝ 1 (α (extChartAt I x₀ x₀, v₀)) (Icc a b)

theorem Poincare.GeodesicTransport.plFlowPosition_contDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t) :
    ContDiffOn ℝ 1
      (fun t : ℝ => (α (extChartAt I x₀ x₀, v₀) t).1) (Icc a b)

theorem Poincare.GeodesicTransport.plFlowCurve_contMDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαtarget : ∀ t ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) t).1 ∈ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ) I 1
      (fun t : ℝ => (extChartAt I x₀).symm
        (α (extChartAt I x₀ x₀, v₀) t).1)
      (Icc a b)

theorem Poincare.GeodesicTransport.plFlowPosition_hasDerivAt_of_mem_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt
      (fun s : ℝ => (α (extChartAt I x₀ x₀, v₀) s).1)
      (α (extChartAt I x₀ x₀, v₀) t).2 t

theorem Poincare.GeodesicTransport.plFlow_chartGeodesicMetric_speed_eq_initial_of_mem_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hε : 0 < ε)
    (hα0 : α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (ht : t ∈ Ioo (-ε) ε) :
    chartGeodesicMetric g x₀
        (α (extChartAt I x₀ x₀, v₀) t).1
        (α (extChartAt I x₀ x₀, v₀) t).2
        (α (extChartAt I x₀ x₀, v₀) t).2 =
      chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀

theorem Poincare.GeodesicTransport.expAt_plFlowCurve_contMDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × E → ℝ → E × E,
        ... -- small velocities get C1 inverse-chart paths
```

The final theorem packages `expAt_uniform_pl_flow_eq_on_Icc` into a usable
positive interval. Since that upstream theorem exports positive `τ₀` and `ε`
but no relation `τ₀ ≤ ε`, this module uses the positive horizon
`τ = min τ₀ ε`. For any small `v₀` and `t ∈ Icc 0 τ`, the packaged curve

```lean
fun s => (extChartAt I x₀).symm
  (α (extChartAt I x₀ x₀, v₀) s).1
```

satisfies `c 0 = x₀`, `c t = expAt g x₀ (t • v₀)`, and
`ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 t)`.

## Isolated blocker

Mathlib's `Manifold.pathELength` is

```lean
pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ
```

and `GeodesicDistance.lean` already provides the bridge

```lean
induced_edist_le_pathELength
```

for a `ContMDiffOn` path. The new file now supplies such a path for the
target-shrunk PL flow. What remains is the exact tangent-norm integrand
bridge for the inverse-chart curve:

```lean
-- Schematic only.
let z := fun s => (α (extChartAt I x₀ x₀, v₀) s).1
let u := fun s => (α (extChartAt I x₀ x₀, v₀) s).2
let c := fun s => (extChartAt I x₀).symm (z s)

∀ s ∈ Ioo 0 t,
  ‖mfderiv% c s 1‖ₑ =
    ENNReal.ofReal
      (Real.sqrt (chartGeodesicMetric g x₀ (z s) (u s) (u s)))
```

After that theorem, `plFlow_chartGeodesicMetric_speed_eq_initial_of_mem_Ioo`
would reduce the integrand to the constant initial speed and the remaining
length computation should be a measure-theory calculation:

```lean
Manifold.pathELength I c 0 t =
  ENNReal.ofReal
    (t * Real.sqrt
      (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀))
```

The available local ingredients are close but not yet assembled:

- `VolumeFinitenessComparison.lean` shows the right chain-rule shape for
  `mfderivWithin` of an inverse-chart path, but only uses an operator-norm
  upper bound, not an exact norm identity.
- `ChartTransport.lean` has `chartMetric_apply`, identifying the metric
  pairing after the inverse-chart tangent map.
- `RiemannianContext.lean` has `ClosedSmoothRiemannianMetric.fiber_inner_eq`,
  identifying Mathlib's installed fiber inner product with `g.inner`.
- The new module has the PL-flow position derivative and constant
  `chartGeodesicMetric` speed on the interior.

The missing bridge is non-vacuous: it must identify the manifold
`mfderiv` of the composed inverse-chart curve with the inverse-chart tangent
map applied to the chart velocity, then rewrite the Riemannian fiber norm
through `fiber_inner_eq` and `chartMetric_apply`. I stopped before inventing
a wrapper around this equality.

## Verification

Commands run:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" Poincare/Global/GeodesicPathLength.lean
lake build Poincare.Global.GeodesicPathLength
```

Actual result:

```text
lake build Poincare.Global.GeodesicPathLength
Build completed successfully (2836 jobs).
```

The build replayed pre-existing imported-module linter warnings. The new
module built successfully, and the forbidden-token grep found no matches.
