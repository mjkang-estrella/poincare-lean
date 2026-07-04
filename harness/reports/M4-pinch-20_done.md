# M4-pinch-20 report

## Scope

Changed only `Poincare/Global/RicciNorm.lean` and this report.  I did not edit
`ScalarVariation.lean` or `ScalarEvolution.lean`.

## Algebra delivered

In namespace `Poincare.PinchingAlgebra`, the diagonal reaction/motion trace is
now pinned as the cubic polynomial

```text
N_react = 10 * R * N - 2 * R^3 - 8 * C
```

where `R = a + b + c`, `N = a^2 + b^2 + c^2`, and
`C = a^3 + b^3 + c^3`.

The exact sign numerator is

```text
R * N_react - 4 * N^2
```

and is proved nonpositive by Schur-form algebra:

```text
R * N_react - 4 * N^2
  = -4 * (a^2(a-b)(a-c) + b^2(b-a)(b-c) + c^2(c-a)(c-b)) <= 0.
```

The Lean proof is actually stronger than the nonnegative-Ricci use case:
`diagonalPinchingReactionSignNumerator3_nonpos` has no sign hypotheses on the
triple.  Positive scalar curvature is only needed to transfer this to the
pinned remainder and quotient signs.

## Main names

- `diagonalRicciCubicTrace3`
- `diagonalRicciNormReactionMotionTrace3_eq_cubic`
- `diagonalPinchingReactionSignNumerator3`
- `diagonalPinchingReactionSignNumerator3_eq_schur`
- `diagonalPinchingReactionSignNumerator3_nonpos`
- `diagonalPinchingReactionRemainder3_eq_scalar_mul_signNumerator3`
- `diagonalPinchingReactionRemainder3_nonpos_of_scalar_pos`
- `diagonalPinchingReactionQuotient3_nonpos_of_scalar_pos`

## Validation points

- `(1,1,2)`: existing `N_react = 32`, existing remainder `= -32`,
  existing quotient reaction `= -1/4`, new numerator `= -16`.
- `(1,2,3)`: existing `N_react = 120`, existing remainder `= -192`,
  existing quotient reaction `= -8/27`, new numerator `= -64`.
- `(1,1,1)`: new `N_react = 12`, new numerator `= 0`; the existing
  space-form lemmas give remainder/quotient `= 0`.
- `(1,0,0)`: new `N_react = 0`, new numerator `= -4`, new remainder `= -2`,
  new quotient reaction `= -4`.  This does not fail; no stronger pinched
  eigenvalue domain is needed for the algebraic sign.

## Manifold transport plan

Next step is to move from diagonal triples to a tangent fiber:

1. Use the spectral theorem for the self-adjoint Ricci endomorphism
   `g.ricciEndoAt x`, with self-adjointness already available as
   `ricciEndoAt_selfAdjoint`.
2. Choose a `g.metricBilinAt x`-orthonormal eigenbasis of the 3D fiber and
   name the eigenvalues `a b c`.
3. Prove trace transport lemmas in that eigenbasis:
   `g.scalarAt x = a + b + c`,
   `g.ricciNormSqAt x = a^2 + b^2 + c^2`, and the metric-motion cubic trace
   equals `4 * (a^3 + b^3 + c^3)`.
4. Bridge the pinned 3D reaction tensor
   `ricciEvolution3ReactionRHSAt` to the diagonal entries
   `3 R lambda - 6 lambda^2 + (2N - R^2)`.
5. Rewrite `pinchingReactionRemainderAt` through the diagonal remainder and
   apply `diagonalPinchingReactionRemainder3_nonpos_of_scalar_pos`.

Missing vocabulary is mostly the orthonormal spectral decomposition for a
self-adjoint endomorphism relative to `g.metricBilinAt x`, plus trace/cubic
trace evaluation lemmas in that eigenbasis.

## Verification

- Forbidden-token scan on `Poincare/Global/RicciNorm.lean`: no matches.
- `lake build Poincare.Global.RicciNorm`: success, with only pre-existing
  warnings in upstream modules and the existing warnings at the top of
  `RicciNorm.lean`.
