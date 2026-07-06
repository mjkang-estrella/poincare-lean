# M5-geo-8 blocked report

## Status

Strict partial progress in `Poincare/Global/GeodesicOverlap.lean`.

The new module builds, but the full chart-overlap geodesic theorem is not
claimed.  The isolated missing step is the Christoffel transformation law on a
chart overlap: a transition-pushed state must satisfy the `y₀` chart
Christoffel ODE whenever the original state satisfies the `x₀` chart ODE and
the pulled-back curve stays in the common source.

The intended route remains reuse-first: derive the overlap transformation from
the two `chartLeviCivita_eventuallyEq_closed` bridges to `g.leviCivita`.
The current API exposes same-anchor ODE uniqueness and each anchor's agreement
with the closed Levi-Civita connection, but it does not yet expose either:

- a naturality theorem turning those two agreement germs into equality of
  model Christoffel fields under a chart transition, or
- a covariant-acceleration formulation of a chart geodesic that can be
  transported across charts and read back as the second component of the
  first-order ODE.

## Added signatures

```lean
def Poincare.GeodesicTransport.chartTransition
    (x₀ y₀ : M) : E → E

def Poincare.GeodesicTransport.chartTransitionDeriv
    (x₀ y₀ : M) (z : E) : E →L[ℝ] E

def Poincare.GeodesicTransport.chartTransitionState
    (x₀ y₀ : M) (γ : ℝ → E × E) : ℝ → E × E

theorem Poincare.GeodesicTransport.chartTransition_apply
theorem Poincare.GeodesicTransport.chartTransitionDeriv_apply
theorem Poincare.GeodesicTransport.chartTransitionState_fst
theorem Poincare.GeodesicTransport.chartTransitionState_snd

theorem Poincare.GeodesicTransport.chartTransitionState_zero
    (x₀ y₀ : M) {γ : ℝ → E × E} {v₀ : E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀)) :
    chartTransitionState x₀ y₀ γ 0 =
      (extChartAt I y₀ x₀,
        chartTransitionDeriv x₀ y₀ (extChartAt I x₀ x₀) v₀)

theorem Poincare.GeodesicTransport.geodesicGermAt_chartTransitionState_fst
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) :
    (fun t : ℝ =>
        (chartTransitionState x₀ y₀
          (geodesicGermChartSolution g x₀ v₀) t).1) =
      fun t : ℝ => extChartAt I y₀ (geodesicGermAt g x₀ v₀ t)

theorem Poincare.GeodesicTransport.geodesicGermAt_chartTransitionState_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) :
    chartTransitionState x₀ y₀ (geodesicGermChartSolution g x₀ v₀) 0 =
      (extChartAt I y₀ x₀,
        chartTransitionDeriv x₀ y₀ (extChartAt I x₀ x₀) v₀)

theorem Poincare.GeodesicTransport.geodesicFlowField_hasDerivAt_of_components

theorem Poincare.GeodesicTransport.geodesicFlowField_eventually_hasDerivAt_of_components

theorem Poincare.GeodesicTransport.chartTransitionState_eventually_solves_of_components
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {γ : ℝ → E × E}
    (hpos : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).1)
        (chartTransitionState x₀ y₀ γ t).2 t)
    (hvel : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).2)
        (-(chartChristoffelField g y₀
            (chartTransitionState x₀ y₀ γ t).1)
          (chartTransitionState x₀ y₀ γ t).2
          (chartTransitionState x₀ y₀ γ t).2) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartTransitionState x₀ y₀ γ)
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀ γ t)) t
```

The last three lemmas isolate the exact two component derivative obligations:
the transition chain rule for the position component and the Christoffel
transformation law for the velocity component.

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicOverlap
```

Actual result:

```text
Build completed successfully (2826 jobs).
```

The build replayed several imported modules and printed pre-existing linter
warnings from those modules.  No new warning was reported for
`Poincare/Global/GeodesicOverlap.lean` in the final successful run.

## Next decomposition

1. Add a chart-overlap Christoffel/naturality theorem:
   from `chartLeviCivita_eventuallyEq_closed` at `x₀` and `y₀`, prove the
   transition-pushed model connection agrees with `chartChristoffelField g y₀`
   on the common chart source.
2. Use that theorem plus the ordinary transition chain rule to prove the full
   transition-transport-of-solutions statement for `chartTransitionState`.
3. Specialize the result to `geodesicGermAt g x₀ v₀` using
   `geodesicGermAt_spec`.
4. Use the germ coherence law to extend geodesics across charts.
5. Combine chart extension with compactness to obtain a uniform extension
   step.
6. Iterate the uniform step to prove geodesic completeness on closed `M`.
