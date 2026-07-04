# M4-pinch-22 blocked: eigenbasis transport layer

## Formalized

- Added the pointwise cubic Ricci trace:
  - `ClosedSmoothRiemannianMetric.ricciCubicTraceAt`
  - `ClosedSmoothRiemannianMetric.ricciCubicTraceAt_eq_trace`
- Added the invariant cubic Ricci-norm reaction/motion trace:
  - `ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceCubicAt`
    for `10 R |Ric|² - 2 R³ - 8 tr(Ric³)`.
- Proved the invariant rewrites in any `Fin 3` Ricci-endomorphism eigenbasis:
  - `scalarAt_eq_sum_eigenvalues_of_ricciEndoAt_eigenbasis`
  - `ricciNormSqAt_eq_sum_eigenvalues_sq_of_ricciEndoAt_eigenbasis`
  - `ricciCubicTraceAt_eq_sum_eigenvalues_cube_of_ricciEndoAt_eigenbasis`
- Proved the diagonal transport layer:
  - `pinchingRicciNormReactionMotionTraceCubicAt_eq_diagonal_of_ricciEndoAt_eigenbasis`
  - `pinchingReactionRemainderAt_eq_diagonal_of_ricciEndoAt_eigenbasis`
- Proved the manifold reaction sign conditional on supplying the spectral
  eigenbasis:
  - `pinchingReactionRemainderAt_nonpos_of_scalar_pos_of_ricciEndoAt_eigenbasis`

This sign theorem uses only the eigenbasis hypothesis and `0 < g.scalarAt x`;
there is no Ricci-nonnegative assumption.

## Stalled boundary

The remaining missing step is producing the `Fin 3` eigenbasis of
`g.ricciEndoAt x` from `g.ricciEndoAt_selfAdjoint x`.

Mathlib has the intended API:

```lean
LinearMap.IsSymmetric.eigenvectorBasis
LinearMap.IsSymmetric.apply_eigenvectorBasis
```

but it applies to the ambient `InnerProductSpace` instance on `TM x`.  The
available symmetry theorem is metric-relative:

```lean
g.inner x (g.ricciEndoAt x u) w =
  g.inner x u (g.ricciEndoAt x w)
```

The pinch campaign's `metricOrthogonalBasisAt` supplies a `g`-orthogonal
algebraic basis, but not yet the transported `InnerProductSpace`/linear-isometry
wrapper needed to feed `g.inner x` to `LinearMap.IsSymmetric.eigenvectorBasis`.

Literal next goal:

```lean
theorem pinchingReactionRemainderAt_nonpos_of_scalar_pos
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hn : n = 3) {x : M} (hRpos : 0 < g.scalarAt x) :
    g.pinchingReactionRemainderAt x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤ 0 := by
  -- produce `b : Module.Basis (Fin 3) ℝ (TM x)` and `μ : Fin 3 → ℝ`
  -- with `∀ i, g.ricciEndoAt x (b i) = μ i • b i` from the
  -- metric-relative self-adjointness of `g.ricciEndoAt x`, then apply
  -- `pinchingReactionRemainderAt_nonpos_of_scalar_pos_of_ricciEndoAt_eigenbasis`.
```

## Verification

- `lake build Poincare.Global.ScalarVariation`
- `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`

Both builds completed successfully.  Remaining output is pre-existing linter
noise in the large dependency chain.

## Step-6 outlook

1. Add a small metric-inner-product fiber wrapper, or an isometry from the
   `g.inner x` fiber to the existing typeclass inner product, so
   `g.ricciEndoAt_selfAdjoint x` becomes a `LinearMap.IsSymmetric` proof.
2. Instantiate `LinearMap.IsSymmetric.eigenvectorBasis` with
   `g.finrank_tangentSpace_eq x` and `hn : n = 3`, then feed the resulting
   basis/eigenvalues into the verified transport theorem above.
3. Apply the closed parabolic maximum-principle machinery to the quotient `Q`,
   using the unconditional quotient evolution, structural gradient damping
   `≤ 0`, and the now-nonpositive reaction term on the positive-scalar domain.
