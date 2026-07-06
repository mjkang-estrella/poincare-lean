# M5-geo-14 done

## Files

- Added `Poincare/Global/GeodesicSpeed.lean`.
- Did not edit existing Lean files, including `Poincare.lean`.

## Main signatures

```lean
abbrev Poincare.GeodesicTransport.chartGeodesicMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ClosedSmoothModel n → ClosedSmoothModel n →L[ℝ]
      ClosedSmoothModel n →L[ℝ] ℝ
```

```lean
theorem Poincare.GeodesicTransport.chartChristoffelField_pairing_eq_blendedChartMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z u v w : ClosedSmoothModel n) :
    chartGeodesicMetric g x₀ z ((chartChristoffelField g x₀ z) u v) w =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (chartGeodesicMetric g x₀) z v) u w) +
          ((fderiv ℝ (chartGeodesicMetric g x₀) z u) v w) -
            ((fderiv ℝ (chartGeodesicMetric g x₀) z w) v u))
```

```lean
theorem Poincare.GeodesicTransport.chart_geodesic_speed_hasDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {γ : ℝ → ClosedSmoothModel n × ClosedSmoothModel n} {t : ℝ}
    (hγ : HasDerivAt γ
      (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) :
    HasDerivAt
      (fun τ : ℝ =>
        chartGeodesicMetric g x₀ (γ τ).1 (γ τ).2 (γ τ).2)
      0 t
```

```lean
theorem Poincare.GeodesicTransport.chart_geodesic_speed_constantOn
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {s : Set ℝ} (hs_open : IsOpen s) (hs_pre : IsPreconnected s)
    {γ : ℝ → ClosedSmoothModel n × ClosedSmoothModel n}
    (hγ : ∀ t ∈ s,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    {t u : ℝ} (ht : t ∈ s) (hu : u ∈ s) :
    chartGeodesicMetric g x₀ (γ t).1 (γ t).2 (γ t).2 =
      chartGeodesicMetric g x₀ (γ u).1 (γ u).2 (γ u).2
```

```lean
theorem Poincare.GeodesicTransport.chart_geodesic_speed_constantOn_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {a b : ℝ} {γ : ℝ → ClosedSmoothModel n × ClosedSmoothModel n}
    (hγ : ∀ t ∈ Ioo a b,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    {t u : ℝ} (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) :
    chartGeodesicMetric g x₀ (γ t).1 (γ t).2 (γ t).2 =
      chartGeodesicMetric g x₀ (γ u).1 (γ u).2 (γ u).2
```

```lean
theorem Poincare.GeodesicTransport.geodesicGermChartSolution_speed_eventually_eq_initial
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (v0 : ClosedSmoothModel n) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      chartGeodesicMetric g x₀
          (geodesicGermChartSolution g x₀ v0 t).1
          (geodesicGermChartSolution g x₀ v0 t).2
          (geodesicGermChartSolution g x₀ v0 t).2 =
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v0 v0
```

## Verification

Command:

```bash
lake build Poincare.Global.GeodesicSpeed
```

Result: success. Final output ended with:

```text
Built Poincare.Global.GeodesicSpeed
Build completed successfully (2826 jobs).
```

The build replayed existing upstream warnings, but emitted no warnings from
`Poincare/Global/GeodesicSpeed.lean` in the final run.

## Next Gauss-lemma decomposition

1. Radial fields: define the radial chart variation from
   `geodesicGermChartSolution g x0 (r • v)` and package the radial velocity
   field as the time derivative of the chosen chart solution. Use the constant
   speed theorem to keep
   `G(gamma_v t) (gamma_v' t) (gamma_v' t)` pinned to its initial value.

2. Polar variation: introduce the two-parameter variation
   `(s, t) ↦ geodesicGermChartSolution g x0 (v + s • w) t`, prove the fixed-time
   endpoint derivative identifies with the chart differential of the exponential
   germ, and prove the mixed time/parameter derivatives commute on the local
   existence rectangle.

3. Pairing identity: differentiate the constant-speed identity in the variation
   parameter and combine it with the compatibility identity already isolated as
   `chartChristoffelField_pairing_eq_blendedChartMetric`. The target bridge is
   the radial Gauss lemma form
   `G(exp_x v) (d exp_x(v) w) (d exp_x(v) v) = G_x w v`, after translating the
   chart statement through the fixed-time exponential germ.
