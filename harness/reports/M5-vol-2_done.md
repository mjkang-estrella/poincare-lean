# M5-vol-2: Riemannian volume measure via Hausdorff measure

Task: Goal 10 opener, define the global Riemannian volume candidate from the
induced metric Hausdorff measure.

## Delivered Lean surface

Added `Poincare/Global/VolumeMeasure.lean`.

Main definition:

```lean
def Poincare.volumeMeasure
    (g : ClosedSmoothRiemannianMetric n M) : MeasureTheory.Measure M :=
  letI : MetricSpace M := g.toMetricSpace
  μH[(n : ℝ)]
```

The module uses `[MeasurableSpace M] [BorelSpace M]` as hypotheses rather than
constructing a local Borel measurable space in the return type.  This keeps the
definition returning an ordinary `Measure M`; `BorelSpace M` records that the
measurable-space instance is the Borel sigma algebra, and after installing
`g.toMetricSpace` this is the Borel structure for the induced Riemannian
topology.

Proven sanity lemmas:

- `volumeMeasure_apply`: definitional reduction to `μH[(n : ℝ)]` after
  installing `g.toMetricSpace`.
- `isOpen_nullMeasurableSet_volumeMeasure`: open sets are null-measurable for
  `volumeMeasure g`, exposing the Borel-measure API.
- `volumeMeasure_noAtoms`: if `0 < n`, then `volumeMeasure g` has no atoms,
  via `MeasureTheory.Measure.noAtoms_hausdorff`.

## What Mathlib gives for free

Mathlib's `MeasureTheory.Measure.hausdorffMeasure`, notation `μH[d]`, is a
measure built from the metric outer-measure construction.  Once the induced
metric and a Borel measurable space are installed, it immediately provides:

- a bona fide `MeasureTheory.Measure M`;
- Borel/open-set measurability through the ambient `BorelSpace M`;
- the covering formula `hausdorffMeasure_apply`;
- monotonicity in dimension via `hausdorffMeasure_mono`;
- zero-or-infinity dimension comparison via `hausdorffMeasure_zero_or_top`;
- no-atoms for positive dimension via `noAtoms_hausdorff`;
- Lipschitz and isometry transport inequalities/equalities for Hausdorff
  measure.

## What is not free

Finiteness of `volumeMeasure g Set.univ` on compact `M` is not a bare compactness
consequence available from this API.  It needs quantitative local control:
finite chart cover, bi-Lipschitz or Lipschitz chart bounds for the induced
Riemannian distance on compact chart domains, and comparison with Euclidean
`μH[n]`/Lebesgue measure.

Strict positivity on every nonempty open set also needs the same local
comparison.  The expected route is to use chart domains, the positive-definite
metric coefficient matrix, and the local density from
`Poincare/Global/VolumeDensity.lean`:

```lean
Poincare.VolumeDensity.chartVolumeDensity G = Real.sqrt |G.det|
```

Then prove that, in smooth charts, `volumeMeasure g` agrees locally with
`withDensity` of Euclidean measure by this density, up to the chosen Hausdorff
normalization.  Positivity follows from positive-definiteness of `G`; finiteness
on compact `M` follows from compactness plus a finite chart subcover and bounded
density on compact chart images.

Scaling under `constSMul` was not encoded here.  Mathlib has Hausdorff measure
transport for isometries and normed-space scalar multiplication, but this
manifold-level definition first needs a theorem identifying how `constSMul` of
a Riemannian metric scales the induced distance.  Once a distance scaling lemma
exists, the Hausdorff scaling statement should follow through the existing
Lipschitz/antilipschitz or homothety API.

## Scalar-curvature integration roadmap

1. Define scalar-curvature functions in the global Riemannian context and prove
   Borel measurability, ideally continuity or smoothness.
2. Prove the chart formula comparing `volumeMeasure g` with
   `sqrt(det G)` times Euclidean Lebesgue/Hausdorff measure.
3. Prove `IsFiniteMeasure (volumeMeasure g)` on closed manifolds.
4. Define total scalar curvature and mean scalar curvature using
   `∫ x, scalarCurvature g x ∂volumeMeasure g`.
5. Add normalized Ricci-flow volume and mean-scalar identities once the
   time-dependent metric, scalar curvature, and volume-measure variation lemmas
   are available.

## Verification

Command:

```text
lake build Poincare.Global.VolumeMeasure
```

Result:

```text
✔ [2714/2714] Built Poincare.Global.VolumeMeasure (2.3s)
Build completed successfully (2714 jobs).
```
