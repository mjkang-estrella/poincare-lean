# M5-glob-10 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/ReanchorLawFinal.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module assembles the strongest available local re-anchor theorem from
the current interfaces.  It discharges the source shifted-ODE plumbing from
the germ radius hypothesis, uses the already-proved first-order chart
transition close from `GeodesicReanchorClose.lean`, and feeds the existing
same-anchor PL uniqueness theorem in `GeodesicReanchor.lean`.

## Verified Lean payload

The file adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_velocity_component
```

It proves

```lean
(fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
  =ᶠ[𝓝 (0 : ℝ)]
geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀)
```

assuming:

- `t₀` lies in the source germ ODE radius;
- `y₀ = geodesicGermAt g x₀ v₀ t₀`;
- the shifted source chart state stays in the `x₀` chart target eventually;
- the shifted manifold germ stays in the `y₀` chart source eventually;
- the remaining velocity-component Christoffel transition law holds:

```lean
∀ᶠ t in 𝓝 (0 : ℝ),
  HasDerivAt
    (fun s : ℝ =>
      (chartTransitionState x₀ y₀
        (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) s).2)
    (-(chartChristoffelField g y₀
        (chartTransitionState x₀ y₀
          (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).1)
      (chartTransitionState x₀ y₀
        (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2
      (chartTransitionState x₀ y₀
        (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2)
    t
```

## Remaining blocker

The unconditional parked law is still blocked exactly where
`M5-geo-24_blocked.md` left it: the current exported APIs still do not prove
the velocity-component Christoffel transition for the double-anchor state.

Concretely, nothing currently proves that differentiating

```lean
fun s =>
  chartTransitionDeriv x₀ y₀
    (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).1
    (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).2
```

along the shifted `x₀` geodesic yields the target-anchor acceleration

```lean
-(chartChristoffelField g y₀
    (chartTransitionState x₀ y₀ γ t).1)
  (chartTransitionState x₀ y₀ γ t).2
  (chartTransitionState x₀ y₀ γ t).2
```

in the `y₀` chart.  The new file proves that this is now the only remaining
analytic input needed by the local germ re-anchor equality.

## Verification

Commands run:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" Poincare/Global/ReanchorLawFinal.lean
git diff --check -- Poincare/Global/ReanchorLawFinal.lean
lake build Poincare.Global.ReanchorLawFinal
```

Actual result:

```text
lake build Poincare.Global.ReanchorLawFinal
✔ [2830/2830] Built Poincare.Global.ReanchorLawFinal (2.3s)
Build completed successfully (2830 jobs).
```

The `rg` forbidden-token scan produced no matches.  The build replayed
pre-existing imported-module warnings, then built the new module successfully.
