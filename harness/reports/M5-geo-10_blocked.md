# M5-geo-10 blocked report

## Status

Strict partial progress in `Poincare/Global/GeodesicReanchor.lean`.

The new module builds and does not edit any existing Lean file.  It proves the
near-anchor cutoff-`1` coefficient representation at the metric and Koszul
pairing levels, and it packages the actual re-anchoring uniqueness step: once
the shifted, transition-transported state is known to solve the current-anchor
chart geodesic ODE, same-anchor uniqueness gives the manifold germ equality.

The full double-good transition law is still blocked.  The remaining missing
step is not general-overlap naturality of the blended Christoffel fields; it is
the local re-anchoring coefficient transformation in the double cutoff-`1`
zone, where both fields reduce to transported Christoffel data for the same
closed metric `g`.

## Added signatures

```lean
theorem Poincare.GeodesicTransport.blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ClosedSmoothModel n} (hz : cutoff (n := n) x₀ z = 1) :
    CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z =
      CovariantDerivative.chartMetric g.inner x₀ z

theorem Poincare.GeodesicTransport.blendedChartMetric_eventuallyEq_chartMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    (fun z : ClosedSmoothModel n =>
        CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀ z)
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners n) x₀ x₀)]
    (fun z : ClosedSmoothModel n => CovariantDerivative.chartMetric g.inner x₀ z)

theorem Poincare.GeodesicTransport.chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ClosedSmoothModel n}
    (hz : ∀ᶠ z' in 𝓝 z, cutoff (n := n) x₀ z' = 1)
    (u v w : ClosedSmoothModel n) :
    CovariantDerivative.chartMetric g.inner x₀ z
        ((chartChristoffelField g x₀ z) u v) w =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z v) u w) +
          ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z u) v w) -
            ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z w) v u))

theorem Poincare.GeodesicTransport.chartChristoffelField_pairing_eq_chartMetric_at_anchor

theorem Poincare.GeodesicTransport.chartChristoffelField_eventually_pairing_eq_chartMetric

def Poincare.GeodesicTransport.reanchoredVelocity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    (v₀ : ClosedSmoothModel n) (t₀ : ℝ) : ClosedSmoothModel n

theorem Poincare.GeodesicTransport.shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    (v₀ : ClosedSmoothModel n) (t₀ : ℝ)
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hy_source : ∀ᶠ s in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ v₀ (t₀ + s) ∈
        (extChartAt (closedSmoothModelWithCorners n) y₀).source)
    (htransport_solves : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt
        (chartTransitionState x₀ y₀
          (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)))
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀
            (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) s))
        s) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀)
```

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicReanchor
```

Actual result:

```text
Build completed successfully (2827 jobs).
```

The build replayed pre-existing imported-module linter warnings.  No failure
or placeholder proof was present in `Poincare/Global/GeodesicReanchor.lean`.

## Isolated blocker

To finish the non-conditional re-anchoring law, prove the double-good
transported-solution statement for

```lean
chartTransitionState x₀ y₀
  (fun s => geodesicGermChartSolution g x₀ v₀ (t₀ + s))
```

under honest neighborhood hypotheses:

- `geodesicGermAt g x₀ v₀ (t₀ + s)` stays in the `y₀` chart source near `s=0`;
- both `cutoff x₀` and `cutoff y₀` are identically `1` as germs at the
  relevant chart base points;
- the shifted `x₀` chart solution remains in the interval where the chosen
  local ODE solution is known.

The coefficient side is now reduced to the proved Koszul pairing formula for
`CovariantDerivative.chartMetric g.inner`.  The missing proof should show that
the second derivative of `chartTransition x₀ y₀` transforms this pairing
formula into the `y₀` chart acceleration term.  Two viable routes remain:

1. Direct chain-rule proof for the chart transition using the paired Koszul
   formulas on both cutoff-`1` germs.
2. Connection route: compare both chart expressions through
   `chartLeviCivita_eventuallyEq_closed`, then identify the transported
   acceleration by applying uniqueness of the closed Levi-Civita connection on
   common test sections.

## Next decomposition

1. Prove the double-good transition component lemma:
   `chartTransitionState` of the shifted `x₀` solution has the `y₀`
   velocity derivative `-Γ_y(v,v)` near `0`.
2. Feed that lemma into
   `shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored` to remove
   the conditional `htransport_solves` hypothesis.
3. Establish existence of such double-good neighborhoods for sufficiently
   small positive `t₀`.
4. Upgrade the germ re-anchoring step to a uniform local extension radius via
   compactness of the closed manifold.
5. Iterate the uniform extension step to obtain geodesic completeness.
