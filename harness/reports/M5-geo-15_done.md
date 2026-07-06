# M5-geo-15 done

## Files

- Added `Poincare/Global/GaussLemmaRadial.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Radial-radial progress

The new module proves the radial-radial Gauss input without variation theory.
It uses the chart geodesic ODE derivative and the constant-speed theorem from
`Poincare.Global.GeodesicSpeed`, then combines them with the existing
`expAt`/`geodesicGermAt` ray law.

Main signatures:

```lean
theorem Poincare.GeodesicTransport.geodesicGermChartSolution_position_hasDerivAt_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun τ : ℝ => (geodesicGermChartSolution g x₀ v₀ τ).1)
        (geodesicGermChartSolution g x₀ v₀ t).2 t
```

```lean
theorem Poincare.GeodesicTransport.geodesicGermChart_radialRadial_gauss_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
          (fun τ : ℝ => (geodesicGermChartSolution g x₀ v₀ τ).1)
          (geodesicGermChartSolution g x₀ v₀ t).2 t ∧
        chartGeodesicMetric g x₀
            (geodesicGermChartSolution g x₀ v₀ t).1
            (geodesicGermChartSolution g x₀ v₀ t).2
            (geodesicGermChartSolution g x₀ v₀ t).2 =
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀
```

```lean
theorem Poincare.GeodesicTransport.expAt_radialRadial_gauss_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∀ᶠ t in 𝓝[Icc (0 : ℝ) τ] (0 : ℝ),
        expAt g x₀ (t • v₀) = geodesicGermAt g x₀ v₀ t ∧
          HasDerivAt
              (fun σ : ℝ => (geodesicGermChartSolution g x₀ v₀ σ).1)
              (geodesicGermChartSolution g x₀ v₀ t).2 t ∧
            chartGeodesicMetric g x₀
                (geodesicGermChartSolution g x₀ v₀ t).1
                (geodesicGermChartSolution g x₀ v₀ t).2
                (geodesicGermChartSolution g x₀ v₀ t).2 =
              chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀
```

## Transverse blocker isolated

The transverse Gauss lemma was not faked.  The new file isolates the exact
ODE-dependence interface needed to continue:

```lean
def Poincare.GeodesicTransport.ChartGeodesicInitialVelocitySmoothDependence
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : Prop :=
  ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E → ℝ → E × E,
    (∀ v₀ : E, ‖v₀‖ < δ →
      Φ v₀ 0 = (extChartAt I x₀ x₀, v₀)) ∧
    (∀ v₀ : E, ‖v₀‖ < δ →
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (Φ v₀)
          (geodesicFlowField (chartChristoffelField g x₀) (Φ v₀ t)) t) ∧
    ContDiffOn ℝ 2 (Function.uncurry Φ)
      (Metric.ball (0 : E) δ ×ˢ Ioo (-ε) ε)
```

This is the concrete missing parametric ODE statement: one common local chart
flow, solving the chart geodesic ODE, with `C²` dependence on initial velocity
and time.  The pinned Mathlib ODE API exposes Lipschitz and `ContinuousOn`
dependence of the Picard-Lindelöf flow on initial data
(`exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` and
`exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`), but I did not
find an exported `ContDiffOn`/Frechet-derivative dependence theorem strong
enough to justify differentiating the constant-speed identity in the initial
velocity parameter or commuting the mixed time/velocity derivatives.

## Verification

Forbidden-token check:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/GaussLemmaRadial.lean
```

Actual result: no matches.

Required build:

```bash
lake build Poincare.Global.GaussLemmaRadial
```

Actual result: success. Final output ended with:

```text
✔ [2833/2833] Built Poincare.Global.GaussLemmaRadial (2.6s)
Build completed successfully (2833 jobs).
```

The build replayed existing upstream warnings, but the final run emitted no
warnings from `Poincare/Global/GaussLemmaRadial.lean`.
