# M4-pinch-3 blocked: closed 3D decomposition instantiation

## Verified progress

- Added the finite-dimensional Euclidean 3D four-linear reconstruction and
  Weyl-vanishing algebra in `Poincare/Global/RicciNorm.lean`.
- New names:
  - `PinchingAlgebra.Euclidean3`
  - `PinchingAlgebra.FourLinearEuclidean3`
  - `PinchingAlgebra.euclidean3Basis`
  - `PinchingAlgebra.fourLinearEuclidean3_basis_ext`
  - `PinchingAlgebra.fourLinearEuclidean3_eq_zero_of_basis`
  - `PinchingAlgebra.fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace`
  - `PinchingAlgebra.fourLinearEuclidean3_apply_eq_zero_of_riemann_symm_and_trace`

The main theorem proves that a bundled four-linear form on
`EuclideanSpace ℝ (Fin 3)` vanishes if it satisfies:

- antisymmetry in the first pair;
- antisymmetry in the second pair;
- pair-exchange symmetry;
- first Bianchi;
- zero standard orthonormal Ricci trace
  `∑ i, W(eᵢ, u, eᵢ, w) = 0`.

The proof is a direct finite component elimination over `Fin 3`: trace equations
kill the three mixed components and the diagonal sectional components, then
four-slot basis extensionality reduces the conclusion to finite cases.

## Remaining blocker

The requested closed-manifold instantiation is not yet a clean application of
the Euclidean lemma.  The closed curvature trace currently exposed by
`ricciAt_eq_curvature_inner_contraction` is the basis/metric-dual contraction

```text
Σᵢ ⟨R(bᵢ, u) w, ♯bⁱ⟩
```

where `b = Module.finBasis ℝ (TM x)` and
`♯bⁱ = metricDualVectorAt g x (b.coord i)`.  The new algebra lemma is stated
for the standard orthonormal trace

```text
Σᵢ W(eᵢ, u, eᵢ, w)
```

on `EuclideanSpace ℝ (Fin 3)`.  These are equivalent only after either:

1. transporting the tangent fiber with its metric `g.inner x` to an
   orthonormal Euclidean basis and proving trace invariance for this 4-linear
   contraction; or
2. generalizing the fiber lemma to an arbitrary basis with the corresponding
   `metricDualVectorAt` trace.

The closed side also still needs public packaging lemmas for the curvature
difference as a bundled four-linear form: additivity/smul in all four slots,
Riemann symmetries for `riemannFromRicci3At`, and the equality of the Ricci
trace of `riemannFromRicci3At` with `g.ricciAt`.  The actual curvature
symmetry lemmas are present (`closedCurvaturePairSymmAt`,
`closedCurvaturePairLastPairAntisymmAt`, `closedCurvatureOp_first_bianchiAt`),
but the Ricci-from-Riemann candidate is not yet exposed in a form that can be
fed into the new bundled algebra theorem without additional infrastructure.

## Next atom

Generalize the algebra lemma to the trace form already used by the closed
metric library:

```text
∀ u w, Σᵢ W(bᵢ, u, w, metricDualVectorAt g x (b.coord i)) = 0
```

or prove a basis-invariance bridge from this contraction to an orthonormal
Euclidean trace.  Then add the missing bundled four-linearity, symmetry, and
trace lemmas for the difference

```text
⟨curvatureOp g.leviCivita (extend p) (extend q) (extend r) x, s⟩
  - g.riemannFromRicci3At x p q r s
```

and apply the generalized vanishing lemma to obtain
`RiemannDeterminedByRicci3At` in dimension three.
