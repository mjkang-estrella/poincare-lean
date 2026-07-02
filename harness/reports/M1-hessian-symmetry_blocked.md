# M1-sharp-map green report

This report supersedes the earlier blocked status for the Hessian symmetry
gradient-regularity bridge.

## Green results

Commit `1655958e` proves the reusable gradient regularity bridge in
`Poincare/Global/Laplacian.lean`:

```lean
theorem ClosedSmoothRiemannianMetric.mdifferentiableAt_gradient
    (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x
```

Implementation route: Route 2 from the previous report.  In the chart at `x`,
the proof builds the smooth blended chart metric `Ghat`, uses the model formula
`RicciFlow.RicciFlow.coordGradient Ghat F z = (Ghat z).inverse (fderiv ℝ F z)`,
pulls the differentiable model vector field back through `extChartAt I x`, and
identifies it locally with `g.gradient f` by metric nondegeneracy and
`chartMetric_apply_chart`.

Commit `9f7fcc3b` proves the no-side-hypothesis Hessian symmetry payoff:

```lean
theorem ClosedSmoothRiemannianMetric.hessianAt_symm'
    (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TM x) :
    g.hessianAt f x v w = g.hessianAt f x w v
```

Commit `ddd1500b` adds the quick Laplacian linearity upgrades with the
gradient-field side hypotheses discharged from pointwise `C²` scalar
regularity:

```lean
theorem ClosedSmoothRiemannianMetric.laplacianAt_add'
theorem ClosedSmoothRiemannianMetric.laplacianAt_const_smul'
```

## Verification

```text
lake build Poincare.Global.Laplacian
Build completed successfully (2801 jobs).
```

Additional local checks on `Poincare/Global/Laplacian.lean`:

```text
forbidden-placeholder scan on Poincare/Global/Laplacian.lean
git diff --check -- Poincare/Global/Laplacian.lean
```

Both checks were clean.
