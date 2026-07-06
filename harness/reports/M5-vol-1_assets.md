# M5-vol-1 assets: Riemannian volume measure

Task: Goal 9, Riemannian volume scoping plus first chart-level density construction.

## Pinned Mathlib inventory

Pinned Mathlib revision from `lake-manifest.json`: `7175569c842f9164564bd76ff8b207e7b4705522`.

### Measures on manifolds

Verdict: no ready Riemannian volume measure on charted manifolds found.

Local source checks:

- `Mathlib/Geometry/Manifold/Measure*.lean`: no files.
- Searches for `Manifold.*Measure`, `Measure.*Manifold`, `charted.*measure`, and manifold-specific `integral` APIs did not find a packaged manifold measure layer.
- `Mathlib/MeasureTheory/Measure/Hausdorff.lean` does define `MeasureTheory.Measure.hausdorffMeasure`, notation `μH[d]`, for any `EMetricSpace`.
- `Mathlib/Geometry/Euclidean/Volume/Measure.lean` defines `MeasureTheory.Measure.euclideanHausdorffMeasure`, notation `μHE[d]`, by scaling Hausdorff measure so it agrees with Euclidean Lebesgue/Haar measure in dimension `d`.

Impact: the repo still needs either a chart-glued volume measure or a theorem-backed decision to use induced-metric Hausdorff measure as the volume measure.

### Induced-metric Hausdorff shortcut

Verdict: promising shortcut, not turnkey.

The repo already has `ClosedSmoothRiemannianMetric.toEMetricSpace` and `toMetricSpace` in `Poincare/Global/RiemannianContext.lean`, built from Mathlib's Riemannian path-length construction. Therefore one can instantiate an induced `EMetricSpace`/`MetricSpace` from `g` and then form `μH[n]` or normalized `μHE[n]` on `M`, provided a compatible `MeasurableSpace M`/`BorelSpace M` is installed.

This may avoid manually gluing measures as the primary definition:

```lean
letI : EMetricSpace M := g.toEMetricSpace
-- with a Borel measurable space:
-- (μHE[n] : MeasureTheory.Measure M)
```

But the missing theorem is the important one: the induced metric Hausdorff measure agrees locally with `sqrt(det G)` times Lebesgue measure in smooth charts, with the right normalization. Without that bridge, scalar-curvature integration would be possible only as integration against an abstract metric Hausdorff measure, not yet as the standard Riemannian volume form used in Ricci-flow calculations.

### Integration of functions on charted spaces

Verdict: generic integration exists; charted-space-specific integration does not.

Mathlib's `MeasureTheory.Integral.*` hierarchy provides Lebesgue and Bochner integration against arbitrary `MeasureTheory.Measure`. This is enough once a measure on `M` exists. I found no manifold-specific API for integrating in charts or transporting integrals across chart transitions.

For scalar curvature integration, remaining requirements are:

- choose/define the measure on `M`;
- install/use the Borel measurable structure for the induced topology;
- prove scalar-curvature functions are measurable or continuous in the relevant Global layer;
- prove finite measure on closed manifolds if using normalized averages.

### Smooth partitions of unity

Verdict: usable for gluing local densities, but it does not itself glue measures.

`Mathlib/Geometry/Manifold/PartitionOfUnity.lean` exists and defines `SmoothPartitionOfUnity`. It includes local finiteness, smoothness, subordinate covers, and in particular an existence theorem subordinate to `chartAt` sources. This is strong enough infrastructure to localize constructions to charts and sum locally finite expressions.

What is missing for volume: a measure-gluing construction theorem saying locally defined measures with overlap compatibility assemble into a global Borel measure. A partition of unity can be used to define integrals by a locally finite sum of chart integrals, but well-definedness under refinement and overlap changes still has to be proved.

### Determinant and density algebra

Verdict: enough for the first chart construction.

Available local ingredients:

- `Matrix.det`, `Matrix.det_one`, `Matrix.det_diagonal`, `Matrix.det_smul`.
- `Matrix.PosDef` in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`; positive-definite matrices are invertible, hence have nonzero determinant.
- `Mathlib/Analysis/Matrix/PosDef.lean` additionally proves `Matrix.PosDef.det_pos`, but it is not in the current olean cache; the first construction avoids that heavier import.
- `Continuous.matrix_det` in `Mathlib/Topology/Instances/Matrix.lean`.
- `Real.sqrt`, `Real.sq_sqrt`, `Real.sqrt_pos`, and continuity of square root/absolute value.

This supports a chart-level density `sqrt |det G|`, positivity under `G.PosDef`, conformal squared density `(sqrt |det (f I)|)^2 = f^n` for `f >= 0`, and continuity in chart coordinates when the Gram matrix is continuous.

## Construction roadmap

1. Formalize chart density as `chartVolumeDensity G = sqrt |G.det|` for finite coordinate Gram matrices, plus a bridge from bilinear forms on `Fin n -> R` to matrices.
2. Define local chart measures by `Measure.withDensity` over the model-space Lebesgue/Haar measure using `ENNReal.ofReal (chartVolumeDensity G)`.
3. Prove overlap compatibility using the metric coefficient transformation rule and a Jacobian/change-of-variables theorem, or pivot to induced `μHE[n]` and prove its local `sqrt(det G)` chart formula.
4. Use `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source` to package local integrals and prove independence from the chosen subordinate partition/chart cover.
5. Define `volumeMeasure (g : ClosedSmoothRiemannianMetric n M) : MeasureTheory.Measure M`, then prove Borel regularity/finite volume on compact `M`, scalar-curvature measurability, and conformal/variation lemmas needed for normalized Ricci flow.

## Current implementation status

Report written before code edits as required.

Added `Poincare/Global/VolumeDensity.lean` with:

- `conformalInnerScale`, a local wrapper for `c • innerSL R`;
- `bilinearFormMatrix` for continuous bilinear forms on `EuclideanSpace R (Fin n)`;
- `chartVolumeDensity G = Real.sqrt |G.det|`;
- positivity from `Matrix.PosDef`;
- conformal squared density for `conformalGram c = c I`: `chartVolumeDensity (conformalGram c)^2 = c^n` for `0 <= c`;
- bilinear-form conformal specialization both under the hypothesis that the coordinate Gram matrix is `c I` and for `conformalInnerScale`;
- continuity of `chartGramDet` and `chartVolumeDensity` for continuous Gram-matrix families.

The raw theorem statement for `(c • innerSL R)` was routed through `conformalInnerScale`: in this pinned Mathlib, `innerSL` elaborates through semilinear/star-linear bundles, and the wrapper matches the repo's existing conformal-metric pattern while exposing the required continuous-bilinear value.

Verification:

```text
lake build Poincare.Global.VolumeDensity
✔ [2393/2393] Built Poincare.Global.VolumeDensity (2.5s)
Build completed successfully (2393 jobs).
```
