# M5-geo-27 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/GeodesicDistance.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module proves the path-infimum bridge needed by the requested upper
bound.  It does not prove the sharp geodesic upper bound or local distance
formula, because the current exported exponential/geodesic APIs still do not
provide the full-interval smooth radial path and path-length computation
needed to instantiate the bridge.

## Added declarations

```lean
theorem Poincare.GeodesicTransport.induced_edist_eq_riemannianEDist
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    letI : EMetricSpace M := g.toEMetricSpace
    edist x y =
      Manifold.riemannianEDist (closedSmoothModelWithCorners n) x y

theorem Poincare.GeodesicTransport.induced_edist_le_pathELength
    (g : ClosedSmoothRiemannianMetric n M)
    (hγ : ContMDiffOn 𝓘(ℝ) (closedSmoothModelWithCorners n) 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    letI : EMetricSpace M := g.toEMetricSpace
    edist x y ≤ Manifold.pathELength (closedSmoothModelWithCorners n) γ a b

theorem Poincare.GeodesicTransport.induced_dist_le_of_pathELength_le_ofReal
    [ConnectedSpace M] (g : ClosedSmoothRiemannianMetric n M)
    (hγ : ContMDiffOn 𝓘(ℝ) (closedSmoothModelWithCorners n) 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) (hL : 0 ≤ L)
    (hLen :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      Manifold.pathELength (closedSmoothModelWithCorners n) γ a b ≤
        ENNReal.ofReal L) :
    letI : MetricSpace M := g.toMetricSpace
    dist x y ≤ L
```

This is the exact Mathlib `PathELength` route used in
`VolumeFinitenessComparison.lean`, packaged for the project metric `g`.

## Isolated blocker

To close stage 1 for the radial exponential curve, the bridge above still
needs an exported theorem of the following shape:

```lean
-- Schematic only.
∃ r > 0, ∀ v, ‖v‖ < r →
  ∃ γ : ℝ → M,
    γ 0 = x₀ ∧ γ 1 = expAt g x₀ v ∧
    ContMDiffOn 𝓘(ℝ) (closedSmoothModelWithCorners n) 1 γ (Icc 0 1) ∧
    Manifold.pathELength (closedSmoothModelWithCorners n) γ 0 1 ≤
      ENNReal.ofReal (Real.sqrt (chartGeodesicMetric g x₀
        (extChartAt (closedSmoothModelWithCorners n) x₀ x₀) v v))
```

The current APIs fall just short:

- `expAt_closed_interval_eq_uniform_pl_flow` exposes the selected `expAt`
  witness on a closed interval through a PL chart flow `α`, but `α` is exported
  with pointwise `HasDerivWithinAt` and target membership, not
  `ContMDiffOn`/`CMDiff` for the manifold curve needed by
  `riemannianEDist_le_pathELength`.
- `expAt_radialRadial_gauss_eventually` and
  `geodesicGermChartSolution_speed_eventually_eq_initial` are germ/eventual
  statements at `0`; they do not compute `pathELength` on an honest interval
  ending at `expAt g x₀ v`.
- `ExponentialRayLawFull.lean` explicitly records that the remaining full
  `expAt = geodesicGermAt` interval law needs a PL-flow/germ position
  identification on the same closed interval.

Therefore I stopped before inventing a vacuous wrapper around the desired
geodesic upper bound.

Stage 2, the radial energy lower bound for competing paths, is still blocked
by the same quantitative lower chart comparison isolated in
`M5-vol-7_blocked.md`: a finite anti-Lipschitz/lower-length estimate for paths
in a chart/normal ball.  Solving that estimate would also unblock the volume
positivity lower-bound thread.

## Verification

Commands run:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" Poincare/Global/GeodesicDistance.lean
git diff --check -- Poincare/Global/GeodesicDistance.lean
lake build Poincare.Global.GeodesicDistance
```

Actual result:

```text
lake build Poincare.Global.GeodesicDistance
Build completed successfully (2834 jobs).
```

The build replayed pre-existing imported-module linter warnings.  The new
module built successfully, and the forbidden-token grep found no matches.

