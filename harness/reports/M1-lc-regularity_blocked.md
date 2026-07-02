# M1-lc-regularity blocked report

## Verified progress

Added and verified:

```lean
CovariantDerivative.leviCivitaConnection_contMDiff
```

in `Poincare/ModelChristoffel.lean`.

Statement shape:

```lean
theorem leviCivitaConnection_contMDiff {k : ℕ∞ω}
    (hGd : Differentiable ℝ G) (hGc : ContDiff ℝ (k + 1) G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    (hGnd : ∀ (y : F) (v : F), (∀ w, G y v w = 0) → v = 0)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hbg : ∀ (x : F) (v w : F), b x v w = G x v w) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnection G hGsymm hGnd (metric_pairing_mdiff G hGd)) k
```

This proves regularity for the Koszul construction on the model space by
identifying it pointwise with the Christoffel-form connection via
`leviCivitaConnection_eq_modelLeviCivita`, then reusing the existing
`modelLeviCivita_contMDiff`.

Verification command:

```bash
lake build Poincare.ModelChristoffel
```

Result: success. The build reported only pre-existing linter warnings.

Commit:

```text
f4bbd645 Prove model Koszul Levi-Civita regularity
```

## Remaining target

The requested global theorem remains unproved:

```lean
CovariantDerivative.ContMDiffCovariantDerivative
  (LeviCivitaExistence.closedLeviCivitaConnection g) 1
```

for `g : ClosedSmoothRiemannianMetric n M`.

## Precise obstruction

The repository has the model and chart-side smoothness ingredients:

- `CovariantDerivative.modelLeviCivita_contMDiff`
- `CovariantDerivative.leviCivitaConnection_contMDiff`
- `CovariantDerivative.chartLeviCivita_contMDiff`
- `CovariantDerivative.contMDiffOn_chartMetric_pairing`
- scalar and bracket chart identities in `Poincare/ChartIdentification.lean`

The missing bridge is not regularity of the model formula itself. It is the
transport/interface theorem saying that, on a chart source, the manifold
Koszul connection `LeviCivitaExistence.closedLeviCivitaConnection g` is the
pushforward/pullback of the model-space chart Levi-Civita connection built
from `chartMetric g x₀` or the locally equal blended chart metric.

Concretely, `ContMDiffCovariantDerivative` requires smoothness of the bundle
hom section

```lean
fun y => TotalSpace.mk' _ y ((closedLeviCivitaConnection g) σ y)
```

for every globally `C^(k+1)` tangent section `σ`. The chart theorem currently
proves smoothness for a covariant derivative on the model space `E`, not for
this manifold bundle-hom section on `M`. I did not find an existing theorem
that transports `chartLeviCivita` to a local `CovariantDerivative` on `M`, nor
one identifying that transported operator with the global Koszul construction.

## Remaining sublemmas

1. Define or expose the chart-transported connection on the chart source:
   pull back a tangent section by `(extChartAt I x₀).symm`, apply
   `chartLeviCivita`, and push the resulting model tangent vector back to
   `TangentSpace I y`.

2. Prove local identification with the global Koszul construction:
   for differentiable `σ`, on a neighborhood of `x₀`,
   the transported chart connection agrees pointwise with
   `CovariantDerivative.leviCivitaConnection g.inner ... σ y`.

3. Prove local regularity of the transported section by composing
   `chartLeviCivita_contMDiff` with the tangent-bundle chart/trivialization.

4. Glue the local regularity statements using
   `contMDiffOn_of_locally_contMDiffOn` to build the global
   `ContMDiffCovariantDerivative` instance for
   `closedLeviCivitaConnection g`.

No forbidden Lean placeholder or oracle declarations were added.
