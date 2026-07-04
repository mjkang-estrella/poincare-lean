# M4-pinch-23 done: eigenbasis witness closes the reaction sign

## Formalized

- Added the Mathlib spectral-theorem import needed for self-adjoint linear maps:
  - `Mathlib.Analysis.InnerProductSpace.Spectrum`
- Proved the pointwise spectral witness:
  - `ClosedSmoothRiemannianMetric.exists_ricciEndoAt_eigenbasis_of_dim_three`

This theorem instantiates the tangent fiber as the metric fiber inner-product
space through `g.toRiemannianBundle`, wraps `g.ricciEndoAt x` as a linear map,
uses `g.ricciEndoAt_selfAdjoint x` to prove `LinearMap.IsSymmetric`, applies
`LinearMap.IsSymmetric.eigenvectorBasis`, and indexes the resulting basis by
`Fin 3` using `finrank_tangentSpace_eq` and `hn : n = 3`.

- Proved the unconditional manifold reaction sign:
  - `ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt_nonpos_of_scalar_pos`

The final theorem has only the dimension and positive-scalar hypotheses:

```lean
theorem pinchingReactionRemainderAt_nonpos_of_scalar_pos
    (hn : n = 3) {x : M} (hRpos : 0 < g.scalarAt x) :
    g.pinchingReactionRemainderAt x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤ 0
```

It produces the eigenbasis/eigenvalue witness and applies the existing diagonal
transport theorem
`pinchingReactionRemainderAt_nonpos_of_scalar_pos_of_ricciEndoAt_eigenbasis`.

## Verification

- `lake build Mathlib.Analysis.InnerProductSpace.Spectrum`
- `lake build Poincare.Global.RicciNorm`
- `lake build Poincare.Global.Laplacian`
- `lake env lean Poincare/Global/ScalarVariation.lean`
- `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`
- `git diff --check`
- Forbidden-token diff scan: no added matches.

The requested combined build completed successfully.  Remaining output is the
pre-existing linter noise in the large dependency chain.

## Maximum-principle outlook

The next target is the closed parabolic maximum principle for the quotient
`Q = |Ric|^2 / R^2`.  The available inputs are now:

1. The unconditional quotient evolution theorem from the step-4/step-6
   assembly.
2. The structural gradient damping term `≤ 0`.
3. The unconditional positive-scalar reaction sign proved here.

The `scalarMinimumAt` / track machinery is the template, but applied to a
maximum of `Q` instead of a minimum of scalar curvature.
