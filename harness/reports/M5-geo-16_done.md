# M5-geo-16 done

## Files

- Added `Poincare/Global/GaussLemmaTransverse.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Frozen transverse identity

The new module proves the pointwise transverse Gauss calculation for a
two-parameter chart-geodesic variation.  The central theorem is:

```lean
theorem Poincare.GeodesicTransport.chart_geodesic_transverse_variation_identity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {Φ : ℝ → ℝ → E × E} {J K : ℝ → E} {s t : ℝ}
    (ht : HasDerivAt (Φ s)
      (geodesicFlowField (chartChristoffelField g x₀) (Φ s t)) t)
    (hJ : HasDerivAt J (K t) t)
    (hs_pos : HasDerivAt (fun σ : ℝ => (Φ σ t).1) (J t) s)
    (hs_vel : HasDerivAt (fun σ : ℝ => (Φ σ t).2) (K t) s)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (Φ s t).1) :
    ∃ pairDeriv speedDeriv : ℝ,
      HasDerivAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀ (Φ s τ).1 (J τ) (Φ s τ).2)
        pairDeriv t ∧
      HasDerivAt
        (fun σ : ℝ =>
          chartGeodesicMetric g x₀ (Φ σ t).1 (Φ σ t).2 (Φ σ t).2)
        speedDeriv s ∧
      pairDeriv = (1 / 2 : ℝ) * speedDeriv
```

This is the requested
`∂_t [G(γ)(∂_s γ, ∂_t γ)] = (1 / 2) ∂_s [G(γ)(∂_t γ, ∂_t γ)]`
identity at a point.  The proof differentiates the pairing in `t`, differentiates
the speed in `s`, uses `chartChristoffelField_pairing_eq_blendedChartMetric`,
uses `chartGeodesicMetric_symm`, and uses
`CovariantDerivative.fderiv_metric_symm` for symmetry of the metric derivative.

Auxiliary proven statements:

```lean
theorem Poincare.GeodesicTransport.chart_geodesic_variation_speed_hasDerivAt
theorem Poincare.GeodesicTransport.chart_geodesic_transverse_pairing_hasDerivAt
```

## Interface bridge and required refinement

The bridge theorem consuming the existing named interface is:

```lean
theorem Poincare.GeodesicTransport.chartGeodesicInitialVelocitySmoothDependence_exists_transverse_variation_identity
```

It unpacks `ChartGeodesicInitialVelocitySmoothDependence` to recover the common
family `Φ`, its initial condition, its time-geodesic ODE, and its `ContDiffOn`
payload.  The final implication records exactly what must still be exported from
the smooth-dependence interface at each `(s, t)`:

- `HasDerivAt (fun σ => (Φ (v + σ • w) t).1) (J t) s`
- `HasDerivAt (fun σ => (Φ (v + σ • w) t).2) (K t) s`
- `HasDerivAt J (K t) t`
- `DifferentiableAt ℝ (chartGeodesicMetric g x₀) (Φ (v + s • w) t).1`

The current interface is not logically vacuous, but it under-shoots the final
transverse Gauss theorem if it is expected to discharge the derivative payload
automatically from `ContDiffOn ℝ 2 (Function.uncurry Φ)`.  A sharpened interface
should either:

1. export these fixed-time `s` derivatives and the mixed derivative
   `∂_t J = K` directly, or
2. export enough `HasFDerivAt`/`HasFDerivWithinAt` data on an open rectangle to
   derive them by product-coordinate calculus.

The orthogonal transverse Gauss conclusion then follows by integrating the
scalar ODE on the common interval: if the `s`-derivative of the speed scalar
vanishes along the variation, the pairing derivative is zero; if the initial
pairing `G(anchor)(w, v)` is zero, the pairing remains zero on that interval.

## Discharge route

Two viable routes remain:

1. Quantitative Picard-Lindelof smooth dependence: upgrade the existing local
   ODE dependence result from continuous/Lipschitz dependence to `C²` dependence
   on initial velocity and time, then expose the coordinate derivative payload
   above.
2. Bespoke Gronwall-difference argument: prove differentiability of the flow
   with respect to initial velocity by finite-difference quotients, derive the
   variational equation, and identify `K = ∂_t J`; this avoids requiring a
   broad exported Mathlib smooth-dependence theorem.

## Verification

Forbidden-token check:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/GaussLemmaTransverse.lean
```

Actual result: no matches.

Required build:

```bash
lake build Poincare.Global.GaussLemmaTransverse
```

Actual result: success. Final output ended with:

```text
✔ [2834/2834] Built Poincare.Global.GaussLemmaTransverse (5.7s)
Build completed successfully (2834 jobs).
```

The build replayed existing upstream warnings; it emitted no warnings from
`Poincare/Global/GaussLemmaTransverse.lean`.
