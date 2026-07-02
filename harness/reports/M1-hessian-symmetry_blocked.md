# M1-hessian-symmetry blocked report

## Green result

Commit `16005044` proves the Hessian symmetry reduction in
`Poincare/Global/Laplacian.lean`:

```lean
theorem ClosedSmoothRiemannianMetric.hessianAt_symm
    (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hgrad : MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
      (T% (g.gradient f)) x)
    (v w : TM x) :
    g.hessianAt f x v w = g.hessianAt f x w v
```

The proof uses the existing definition of `hessianAt`.  It extends `v` and
`w` by Mathlib's `extend`, applies `g.leviCivita_metricCompatibleAt` to rewrite
the two Hessian slots as scalar directional derivatives minus gradient pairings
with `∇X` and `∇Y`, uses `g.leviCivita_torsionFreeAt` to identify the
connection skew part with `VectorField.mlieBracket`, and closes the scalar
commutator with `extDerivFun_apply_mlieBracket`.

Verified:

```text
lake build Poincare.Global.Laplacian
Build completed successfully (2791 jobs).
```

## Remaining block

The requested no-side-hypothesis theorem, where `hgrad` is derived from
`hf : ContMDiffAt I 𝓘(ℝ) 2 f x`, is still blocked by the global gradient
regularity bridge.

The definition

```lean
g.gradientAt f x =
  (LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)).symm
    (LinearMap.toContinuousLinearMap.symm (extDerivFun f x))
```

is fiberwise.  The current global API exposes smoothness of the metric pairing
(`g.contMDiff_inner`, `ContMDiffAt.inner_bundle`,
`MDifferentiableAt.inner_bundle`) and the model-space result
`RicciFlow.differentiableAt_coordGradient`, but it does not yet expose a
manifold-level smooth bundle map for the inverse metric / musical sharp map, nor
a local-frame theorem saying that the coefficients of `g.gradient f` are the
smooth inverse of the metric coefficient matrix applied to the coefficients of
`df`.

An honest completion route is one of:

1. Add a local-frame coefficient lemma: in a tangent local frame `e`, prove the
   coefficient vector of `g.gradient f` is `G(y)^{-1} * df_e(y)`, use smoothness
   of `G` from `g.contMDiff_inner`, smoothness of `G^{-1}` by matrix/operator
   inversion, and `mdifferentiableAt_iff_localFrame_coeff`.
2. Add a reusable smooth bundle hom for the Riemannian sharp map
   `T^*M -> TM`, prove it is `C^1` from the smooth metric, and compose it with
   the `C^1` differential field supplied by `hf : C^2`.

Until one of those bridges exists, the theorem above is the strongest verified
statement for the existing `hessianAt` definition without inserting a vacuous
regularity certificate.
